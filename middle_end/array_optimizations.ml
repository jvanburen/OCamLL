(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*            Sinan Supple & Jacob Van Buren, Carnegie Mellon Univ.       *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2016--2017 Supple Productions                              *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

let pass_name = "optimize-array-accesses"
let () = Clflags.all_passes := pass_name :: !Clflags.all_passes

module VarMap = Map.Make (Variable)
type atom = | IntAtom of int | LenAtom of Variable.t | VarAtom of Variable.t
type upperBound = | UBUndef | UB of atom option
type lowerBound = | LBUndef | LB of int option
(* Ranges are half-open *)
type scalarConstraint = lowerBound * upperBound
type boolConstraints = {
    iftrue: scalarConstraint VarMap.t;
    iffalse: scalarConstraint VarMap.t;
  }
type varInfo =
  | BoolInfo of boolConstraints
  | ScalarInfo of scalarConstraint
                             

let merge_atom atomA atomB = match (atomA, atomB) with
    (IntAtom i, IntAtom j) -> Some (IntAtom (max i j))
  | (LenAtom v1, LenAtom v2) -> if v1 = v2 then Some (LenAtom v1) else None
  | (VarAtom v1, VarAtom v2) -> if v1 = v2 then Some (VarAtom v1) else None
  | _ -> None
                                 
