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

let analyze_and_ignore (expr : Flambda.t) : Flambda.t =
  let emptyMap = Lattice.VarMap.empty in
  let (_, _) = try (Array_optimizations.add_constraints emptyMap expr) with
               | ex -> let () = print_string ("Got an exception\n" ^ Printexc.to_string ex) in
                      (emptyMap, Array_optimizations.Lattice.NoInfo)
  in expr

let optimize_array_accesses (program : Flambda.program) : Flambda.program =
  if !Clflags.opticomp_enable
  then Flambda_iterators.map_exprs_at_toplevel_of_program program
        ~f:analyze_and_ignore
  else (print_string "not optimizing arrays because flag was not enabled\n"; program)
