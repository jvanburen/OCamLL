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

open Array_optimizations
let x : Lattice.t = Lattice.bot

(* TODO: generate lattice for entire program and store in a ref, using
  iterators from flambda_iterators.mli
  We shouldn't need to iterate until quiescence because we don't deal with
  mutable variables


  TODO: using lattice info, use a map function from flambda_iterators
  to update the code

  TODO: array accesses in for-loops: should we be hoisting out a bounds check?
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
     Flambda.If_then_else (v, optimize_array lattice thenB,
                           optimize_array lattice elseB)
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
  | Flambda.For _ -> expr
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
  | Flambda.Prim (prim, _, _) ->
     (match prim with
     | Lambda.Parrayrefs _ ->
        let _ = print_string "Got an array reference\n" in
        named
     | Lambda.Parraysets _ ->
        let _ = print_string "Setting an array\n" in
        named
     | _ -> named)
let analyze_and_ignore (expr : Flambda.t) : Flambda.t =
  let emptyMap = Lattice.VarMap.empty in
  let (lattice, _) = try (Array_optimizations.add_constraints emptyMap expr) with
                     | ex -> let () = print_string ("Got an exception\n" ^ Printexc.to_string ex) in
                             (emptyMap, Array_optimizations.Lattice.NoInfo)
  in
  let _ = print_string ("Lattice is: " ^ (Lattice.to_string lattice) ^ "\n") in
  let _ = optimize_array lattice expr in
  expr

let optimize_array_accesses (program : Flambda.program) : Flambda.program =
  if !Clflags.opticomp_enable
  then Flambda_iterators.map_exprs_at_toplevel_of_program program
        ~f:analyze_and_ignore
  else program
