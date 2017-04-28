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


type atom = | IntAtom of int | LenAtom of Variable.t | VarAtom of Variable.t
type upperBound = | POSINF | Atom of atom
type lowerBound = | NEGINF | Zero
(* Ranges are half-open *)
type range = lowerBound * upperBound
                             

let merge_atom atomA atomB = match (atomA, atomB) with
    (IntAtom i, IntAtom j) -> Some (IntAtom (max i j))
  | (LenAtom v1, LenAtom v2) -> if v1 = v2 then Some (LenAtom v1) else None
  | (VarAtom v1, VarAtom v2) -> if v1 = v2 then Some (VarAtom v1) else None
  | _ -> None
(* Take the worse of the two intervals *)
let merge_intervals (lb1, ub1) (lb2, ub2) =
  ((match (ub1, ub2) with
    | (POSINF, _) -> POSINF
    | (_, POSINF) -> POSINF
    | (Atom a, Atom b) -> match merge_atom a b with
                          | Some atom -> Atom atom
                          | None -> POSINF),
   (match (lb1, lb2) with
    | (NEGINF, _) -> NEGINF
    | (_, NEGINF) -> NEGINF
    | (Zero, Zero) -> Zero))
                                 
