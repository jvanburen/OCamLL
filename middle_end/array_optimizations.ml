(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*            Sinan Supple & Jacob Van Buren, Carnegie Mellon Univ.       *)
(*                                                                        *)
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

module VarMap = Variable.Map (*  Map.Make (Variable) *)
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
  | Other
type lattice = varInfo VarMap.t
let getVarInfo (var : Variable.t) (map : lattice) =
  if VarMap.mem var map
  then VarMap.find var map
  else Other
                
let merge_atom atomA atomB = match (atomA, atomB) with
  | (IntAtom i, IntAtom j) -> Some (IntAtom (min i j))
  | (LenAtom v1, LenAtom v2) -> if v1 = v2 then Some (LenAtom v1) else None
  | (VarAtom v1, VarAtom v2) -> if v1 = v2 then Some (VarAtom v1) else None
  | _ -> None

(* TODO: Check for correctness *)
let merge_upper_bound ub1 ub2 =
  match (ub1, ub2) with
  | (UBUndef, _) -> ub2
  | (_, UBUndef) -> ub1
  | (UB (Some atom1), UB (Some atom2)) -> UB (merge_atom atom1 atom2)
  | _ -> UB None

let merge_lower_bound lb1 lb2 =
  match (lb1, lb2) with
  | (_, LBUndef) -> lb1 
  | (LBUndef, _) -> lb2
  | (LB (Some x), LB (Some y)) -> LB (Some (min x y))
  | _ -> LB None
(* TODO: Actually merge the two constraints*)
let merge_bool_constraints (_ : boolConstraints) (_ : boolConstraints) =
  {iffalse = VarMap.empty; iftrue = VarMap.empty}
let merge_scalars (lb1, ub1) (lb2, ub2) = (merge_lower_bound lb1 lb2,
                                           merge_upper_bound ub1 ub2)
let merge_var_info vi1 vi2 =
  match (vi1, vi2) with
  | (BoolInfo bc1, BoolInfo bc2) -> BoolInfo (merge_bool_constraints bc1 bc2)
  | (ScalarInfo si1, ScalarInfo si2) -> ScalarInfo (merge_scalars si1 si2)
  | (Other, y) -> y
  | (x, Other) -> x
  (* TODO: This should be impossible. Raise an exception? *)
  | _ -> Other

let rec add_constraints (known : lattice) (flam : Flambda.t) : (lattice * varInfo) =
  match flam with
  | Flambda.Var v -> (known, getVarInfo v known)
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body; _} ->
     let (known, deInfo) = add_constraints_named known defining_expr in
     let known = VarMap.add var deInfo known in
     add_constraints known body
  (* Right now, we ignore mutable variables. no memory woohoo *)
  | Flambda.Let_mutable {Flambda.body; _} -> add_constraints known body
  | Flambda.Let_rec (defs, body) ->
     let add_def known (name, def) =
       let (known, defInfo) = add_constraints_named known def
       in (VarMap.add name defInfo known) in
     let known = List.fold_left add_def known defs in
     add_constraints known body
  (* We don't known anything about functions right now, although maybe we ought to.
   * Note that in flambda, apply is var(var, var, ...) so we can't gleam any more info
   * by traversing. *)
  | Flambda.Apply _ -> (known, Other)
  (* Object oriented stuff, ew *)
  | Flambda.Send _ -> (known, Other)
  (* Assignment of a mutable variable. We might want to return to this later *)
  | Flambda.Assign _ -> (known, Other)
  | Flambda.If_then_else (_, trueBranch, falseBranch) ->
     (* TODO: Do we need to add the iftrue/iffalse information in some fashion 
      * while analyzing the branches? *)
     let (known, trueInfo) = add_constraints known trueBranch in
     let (known, falseInfo) = add_constraints known falseBranch in
     (known, merge_var_info trueInfo falseInfo)
  | Flambda.Switch (_, {Flambda.consts; Flambda.blocks; Flambda.failaction}) ->
     let add_case (known, possibleInfos) (_, case) =
       let (known, caseInfo) = add_constraints known case
       in (known, caseInfo :: possibleInfos)
     in
     let (known, possibleInfos) =
       List.fold_left add_case (List.fold_left add_case (known, []) consts) blocks
     in
     let switchInfo = List.fold_left merge_var_info Other possibleInfos in
     (match failaction with
     | None -> (known, switchInfo)
     | Some action -> let (known, actionInfo) = add_constraints known action in
                      (known, merge_var_info switchInfo actionInfo))
  | Flambda.String_switch (_, cases, fallthrough) ->
     let add_case (known, possibleInfos) (_, case) = 
       let (known, caseInfo) = add_constraints known case
       in (known, caseInfo :: possibleInfos) in
     let (known, possibleInfos) = List.fold_left add_case (known, []) cases in
     let switchInfo = List.fold_left merge_var_info Other possibleInfos in
     (match fallthrough with
      | None -> (known, switchInfo)
      | Some action -> let (known, actionInfo) = add_constraints known action in
                       (known, merge_var_info switchInfo actionInfo))
  | Flambda.Try_with (exp, _, handler) ->
     let (known, expInfo) = add_constraints known exp in
     let (known, handlerInfo) = add_constraints known handler in
     (known, merge_var_info expInfo handlerInfo)
  | Flambda.While (cond, body) ->
     let (known, _) = add_constraints known cond in
     let (known, _) = add_constraints known body in
     (* In general, we can't know anything about a while loop because who knows if the 
      * condition will ever be true *)
     (known, Other)

  | Flambda.For { Flambda.body; _; } -> add_constraints known body
  | Flambda.Proved_unreachable -> (known, Other)
  | _ -> (known, Other)
and add_constraints_named (known : lattice) (named : Flambda.named) : (lattice * varInfo) =
  match named with
  (* TODO implement properly *)
  | Flambda.Symbol _ -> (known, Other)
  | Flambda.Const _ -> (known, Other)
  | Flambda.Allocated_const _ -> (known, Other)
  | _ -> (known, Other)
