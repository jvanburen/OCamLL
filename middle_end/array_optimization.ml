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

let rec optimize_array (lattice: Lattice.t) (expr : Flambda.t) : Flambda.t =
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
       match (Lattice.getKey_opt (Key.of_var low) lattice,
              Lattice.getKey_opt (Key.of_var hi) lattice) with
       | (Some (ScalarInfo {lb=lbLow;}),
          Some (ScalarInfo {ub=ubHi;})) ->
          ScalarInfo {lb=lbLow; ub=ubHi}
       | _ -> Anything
     in
     let bound_info = (match direction with
                      | Asttypes.Downto -> createConstraint to_value from_value
                      | Asttypes.Upto -> createConstraint from_value to_value)
     in
     let lattice = Lattice.updateVar bound_var bound_info lattice in
     Flambda.For {bound_var; from_value; to_value; direction;
                  Flambda.body = optimize_array lattice body}
  | Flambda.Proved_unreachable -> expr

and optimize_array_named (lattice : Lattice.t) (named : Flambda.named) = (
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
)
(* Oh no, globals! *)
(* let latticeRef = ref Lattice.bot *)

let analyze_expr (expr : Flambda.t) (sigma : Lattice.t) : (Lattice.t * Lattice.varInfo) = (
  let tup = try add_constraints expr sigma
            with ex ->
              (print_string ("Got an exception\n" ^ Printexc.to_string ex);
               Format.print_newline();
               (sigma, Anything)) in
  (print_string "Lattice is:";
  Lattice.print Format.std_formatter sigma;
  Format.print_newline ();
  tup)
)

let rec analyze_program_body (program_body : Flambda.program_body)
                             (sigmaTL : Lattice.t) : Lattice.t =
  let analyze_closure_entry (_ : Variable.t)
                            (fdecl : Flambda.function_declaration)
                            (sigma : Lattice.t) : Lattice.t = (
    let sigma2 = Lattice.addFreeVars (fdecl.Flambda.free_variables) sigma in
    let (sigma3, _) = analyze_expr fdecl.Flambda.body sigma2 in
    sigma3
  )in
  let analyze_set_of_closures {Flambda.function_decls}
                              (sigma : Lattice.t) : Lattice.t =
    Variable.Map.fold analyze_closure_entry function_decls.Flambda.funs sigma
  in
  let analyze_block_field sym (field, idx) sigma_acc : Lattice.t =
    let info = match field with
               | Flambda.Symbol s -> Lattice.getSymField_top (s, idx) sigma_acc
               | Flambda.Const const ->
                  (match const with
                   | Flambda.Int i -> ScalarInfo (SC.of_int i)
                   | Flambda.Char _ -> Anything
                   | Flambda.Const_pointer _ -> Anything) in
    Lattice.updateSymField sym idx info sigma_acc
  in
  let analyze_const_def_val (sym, constant_defining_value)
                                      (sigma : Lattice.t) : Lattice.t =
    match constant_defining_value with
    | Flambda.Set_of_closures set_of_closures ->
        analyze_set_of_closures set_of_closures sigma
    | Flambda.Block (_, constant_defining_fields) ->
        let ifields = List.mapi (fun i s -> (s, i)) constant_defining_fields in
        List.fold_right (analyze_block_field sym) ifields sigma
    | Flambda.Allocated_const ac -> (
            let info = (match ac with
                       | Allocated_const.Int32 i -> ScalarInfo (SC.of_int32 i)
                       | Allocated_const.Int64 i -> ScalarInfo (SC.of_int64 i)
                       | Allocated_const.Nativeint ni -> ScalarInfo (SC.of_nativeint ni)
                       | _ -> Anything) in
            Lattice.updateSymField sym 0 info sigma)
    | Flambda.Project_closure _ -> Lattice.updateSymField sym 0 Anything sigma
  in
  match program_body with
  | Flambda.Let_symbol (_, (Flambda.Set_of_closures set_of_closures), program') ->
      let sigma = analyze_set_of_closures set_of_closures sigmaTL in
      analyze_program_body program' sigma
  | Flambda.Let_symbol (sym, const_defining_value, program') ->
      let sigma = analyze_const_def_val (sym, const_defining_value) sigmaTL in
      analyze_program_body program' sigma
  | Flambda.Let_rec_symbol (symDefList, program') ->
      let sigma = List.fold_right analyze_const_def_val symDefList sigmaTL in
      analyze_program_body program' sigma
  | Flambda.Initialize_symbol (symbol, _, fields, program') ->
        let analyze_expr_field (expr, idx) sigma : Lattice.t =
          let (sigma', info) = analyze_expr expr sigma in
          Lattice.updateSymField symbol idx info sigma'
        in
        let ifields = List.mapi (fun i s -> (s, i)) fields in
        let sigma = List.fold_right analyze_expr_field ifields sigmaTL in
        analyze_program_body program' sigma
  | Flambda.Effect (expr, program') ->
        let (sigma, _) = analyze_expr expr sigmaTL in
        analyze_program_body program' sigma
  | Flambda.End _ -> (print_string "end analyze_toplevel_of_program";
                      print_newline();
                      sigmaTL)

let optimize_array_accesses (program : Flambda.program) : Flambda.program =
  if !Clflags.opticomp_enable
  then let sigma = analyze_program_body program.Flambda.program_body Lattice.bot
       in Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:(optimize_array sigma)
  else program