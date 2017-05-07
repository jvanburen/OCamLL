(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                      Jacob Van Buren, Sinan Cepel                      *)
(*                                                                        *)
(*   Copyright 2013--2016 Supple Productions                              *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let pass_name = "optimize-array-accesses"
let () = Pass_wrapper.register ~pass_name:pass_name

open Array_analysis
open Array_lattice
let x : Lattice.t = Lattice.bot

(* TODO: generate lattice for entire program and store in a ref, using
  iterators from flambda_iterators.mli
  We shouldn't need to iterate until quiescence because we don't deal with
  mutable variables

  TODO: using lattice info, use a map function from flambda_iterators
  to update the code

  TODO: array accesses in for-loops: should we be hoisting out a bounds check?

  TODO: add free variables lattice before looking into functions

  TODO-Someday: check for physical equality before creating a new node
      (important GC speed optimization)
*)

let rec optimize_array (lattice: Lattice.t) (expr : Flambda.t) =
  match expr with
  | Flambda.Var _ -> expr
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body} ->
     Flambda.create_let var
                        (optimize_array_named lattice defining_expr)
                        (optimize_array lattice body)
  | Flambda.Let_mutable _ -> expr
  | Flambda.Let_rec _ -> expr
  | Flambda.Apply _ -> expr
  | Flambda.Send _ -> expr
  | Flambda.Assign _ -> expr
  | Flambda.If_then_else (v, thenB, elseB) ->
     let sigmaTF = Lattice.computeBoolInfo (Key.of_var v) lattice in
     Flambda.If_then_else (v, optimize_array sigmaTF.ifTrue thenB,
                              optimize_array sigmaTF.ifFalse elseB)
  | Flambda.Switch _ -> expr
  | Flambda.String_switch _ -> expr
  | Flambda.Static_raise _ -> expr
  | Flambda.Static_catch _ -> expr
  | Flambda.Try_with (e1, exn, e2) ->
     Flambda.Try_with (optimize_array lattice e1,
                       exn,
                       optimize_array lattice e2)
  | Flambda.While (e1, e2) -> Flambda.While (optimize_array lattice e1,
                                             optimize_array lattice e2)
  | Flambda.For {Flambda.bound_var; Flambda.from_value;
                 Flambda.to_value; Flambda.direction;
                 Flambda.body} ->
     let createConstraint low hi =
       match (Lattice.getVarOpt lattice low, Lattice.getVarOpt lattice hi) with
       | (Some (Lattice.ScalarInfo (lbLow, _)),
          Some (Lattice.ScalarInfo (_, ubHi))) ->
          Lattice.ScalarInfo (lbLow, ubHi)
       | _ -> Lattice.NoInfo
     in
     let bound_info = (match direction with
                      | Asttypes.Downto -> createConstraint to_value from_value
                      | Asttypes.Upto -> createConstraint from_value to_value)
     in
     let lattice = Lattice.addVarInfo bound_var bound_info lattice in
     Flambda.For {bound_var; from_value; to_value; direction;
                  Flambda.body = optimize_array lattice body}
  | Flambda.Proved_unreachable -> expr
and optimize_array_named (lattice : Lattice.t) (named : Flambda.named) =
  match named with
  | Flambda.Symbol _ -> named
  | Flambda.Const _ -> named
  | Flambda.Allocated_const _ -> named
  | Flambda.Read_mutable _ -> named
  | Flambda.Read_symbol_field _ -> named
  | Flambda.Set_of_closures _ -> named
  | Flambda.Project_closure _ -> named
  | Flambda.Move_within_set_of_closures _ -> named
  | Flambda.Project_var _ -> named
  | Flambda.Expr expr -> Flambda.Expr (optimize_array lattice expr)
  | Flambda.Prim (prim, vars, di) ->
     (match prim with
     | Lambda.Parrayrefs arr_kind ->
        let _ = print_string "Got an array reference\n" in
        Flambda.Prim (Lambda.Parrayrefu arr_kind, vars, di)
     | Lambda.Parraysets arr_kind ->
        let _ = print_string "Setting an array\n" in
        let _ = print_string ((string_of_int (List.length vars)) ^ " " ^ (listToString "" (List.map Variable.unique_name vars)) ^"\n") in
        Flambda.Prim (Lambda.Parraysetu arr_kind, vars, di)
     | _ -> named)
(* Oh no, globals! *)
let latticeRef = ref Lattice.bot
let analyze_and_ignore (expr : Flambda.t) : Lattice.varInfo =
  let (lattice, varInfo) = try (add_constraints (!latticeRef) expr) with
                     | ex -> let () = print_string ("Got an exception\n" ^ Printexc.to_string ex) in
                             (!latticeRef, Lattice.NoInfo)
  in
  let _ = latticeRef := lattice in
  let _ = print_string ("Lattice is: " ^ (Lattice.to_string lattice) ^ "\n") in
  varInfo

let analyze_toplevel_of_program ({Flambda.program_body} : Flambda.program) =
  let iter_set_of_closures {Flambda.function_decls} =
    Variable.Map.map (fun (fdecl: Flambda.function_declaration) ->
        let body = fdecl.Flambda.body in
        analyze_and_ignore body) (function_decls.Flambda.funs) in
  let iter_constant_defining_value (sym, constant_defining_value) =
    match constant_defining_value with
    | Flambda.Set_of_closures set_of_closures ->
       let _ = iter_set_of_closures set_of_closures in ()
    | Flambda.Block (_, constant_defining_fields) ->
     let handle_field idx field =
       match field with
       | Flambda.Symbol s ->
          (match Lattice.getSymOpt (!latticeRef) s with
           | Some info -> info
           | None -> Lattice.SymbolField (s, idx))
       | Flambda.Const const ->
          (match const with
           | Flambda.Int i -> Lattice.ScalarInfo (SC.of_int i)
           | Flambda.Char _ -> Lattice.NoInfo
           | Flambda.Const_pointer _ -> Lattice.NoInfo) in
     let defnList = List.mapi handle_field constant_defining_fields in
     latticeRef := Lattice.addSymInfo sym (Lattice.SymInfo defnList) (!latticeRef)
    | Flambda.Allocated_const ac ->
     let info = (match ac with
                 | Allocated_const.Int32 i -> Lattice.ScalarInfo (SC.of_int32 i)
                 | Allocated_const.Int64 i -> Lattice.ScalarInfo (SC.of_int64 i)
                 | Allocated_const.Nativeint ni -> Lattice.ScalarInfo (SC.of_nativeint ni)
                 | _ -> Lattice.NoInfo) in
     latticeRef := Lattice.addSymInfo sym (Lattice.SymInfo [info]) (!latticeRef)
    | Flambda.Project_closure _ ->
       latticeRef := Lattice.addSymInfo sym (Lattice.SymInfo [Lattice.NoInfo]) (!latticeRef) in
  let rec iter_program_body (program : Flambda.program_body) =
  match program with
  | Flambda.Let_symbol (_, Flambda.Set_of_closures set_of_closures, program') ->
     (* TODO Should we do this *)
     let _ = iter_set_of_closures set_of_closures in
     iter_program_body program'
  | Flambda.Let_symbol (sym, const_defining_value, program') ->
     iter_constant_defining_value (sym, const_defining_value);
     iter_program_body program'
  | Flambda.Let_rec_symbol (symDefList, program') ->
     List.iter iter_constant_defining_value symDefList;
     iter_program_body program'
  | Flambda.Initialize_symbol (symbol, _, fields, program') ->
     let varInfos = List.map analyze_and_ignore fields in
     latticeRef := (Lattice.addSymInfo symbol (Lattice.SymInfo varInfos) (!latticeRef));
     iter_program_body program'
  | Flambda.Effect (expr, program') ->
     let _ = analyze_and_ignore expr in
     iter_program_body program'
  | Flambda.End _ -> print_string "end\n"
  in
  iter_program_body program_body

let optimize_array_accesses (program : Flambda.program) : Flambda.program =
  if !Clflags.opticomp_enable
  then (analyze_toplevel_of_program program;
        Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:(optimize_array !latticeRef))
  else program
