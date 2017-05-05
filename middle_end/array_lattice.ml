(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*            Sinan Supple & Jacob Van Buren, Carnegie Mellon Univ.       *)
(*                                                                        *)
(*                                                                        *)
(*   Copyright 2013--2016 Van Buren Enterprises                           *)
(*   Copyright 2016--2017 Supple Productions                              *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

exception Impossible
exception TypeMismatch


let listToString header (list : string list) = header ^ "[" ^ (String.concat ", " list) ^ "]"
(* module type BOUNDED_SEMILATTICE =
sig
  type t
  val bot : t
  val top : t option
  val join : t -> t -> t
  val merge : t -> t -> t
  val leq : t -> t -> bool
  exception WeirdOp of t * t
end *)

(* TODO: implement widening operator *)
module Widening =
struct
  let min x y = Pervasives.min x y
  let max x y = Pervasives.max x y
end

module UpperBound =
struct
  type atom =
    | IntAtom of int64
    | LenAtom of Variable.t
    (* | VarAtom of Variable.t *)
  type t =
    | PosInf
    | UB of atom
    | InclusiveUB of atom
    | Undef
  let (bot, top) = (Undef, PosInf)

  (* Don't use this externally... not sure how to hide, there's no `local` kw *)
  let atomOp oper s k a b =
    match (a, b) with
    | (IntAtom x, IntAtom y) -> s (IntAtom (oper x y)) (* TODO: add widening operator *)
    | (LenAtom x, LenAtom y) -> if x = y then s a else k ()
    (* | (VarAtom x, VarAtom y) -> if x = y then s a else k () *)
    | _ -> k ()

  (* TODO-someday: handle join/merge for inclusiveUB and UB *)
  let join a b =
    match (a, b) with
    | (Undef, other) -> other
    | (other, Undef) -> other
    | (UB aa, UB bb) -> atomOp Widening.max (fun x -> UB x) (fun () -> top) aa bb
    | (InclusiveUB aa, InclusiveUB bb) ->
       atomOp Widening.max (fun x -> InclusiveUB x) (fun () -> top) aa bb
    | _ -> top
  let meet a b =
    match (a, b) with
    | (PosInf, other) -> other
    | (other, PosInf) -> other
    | (UB aa, UB bb) -> atomOp Widening.min (fun x -> UB x) (fun () -> bot) aa bb
    | (InclusiveUB aa, InclusiveUB bb) ->
       atomOp Widening.min (fun x -> InclusiveUB x) (fun () -> bot) aa bb
    | _ -> bot
  let leq a b = (join a b) = b
  let atom_to_string atom =
    match atom with
    | LenAtom var -> "LenAtom " ^ (Variable.unique_name var)
    (* | (* VarAtom *) var -> "VarAtom " ^ (Variable.unique_name var) *)
    | IntAtom i -> "IntAtom " ^ (Int64.to_string i)

  let to_string (t : t) =
    match t with
    | PosInf -> "PosInf"
    | UB atom -> "UB " ^ (atom_to_string atom)
    | InclusiveUB atom -> "UBInclusive " ^ (atom_to_string atom)
    | Undef -> "Undef"
end
module UB = UpperBound (* Abbreviation *)

module LowerBound =
struct
  type t =
    | NegInf
    | LB of int64
    | Undef
  let (bot, top) = (Undef, NegInf)

  let join a b =
    match (a, b) with
    | (Undef, other) -> other
    | (other, Undef) -> other
    | (LB aa, LB bb) -> LB (Widening.min aa bb)
    | _ -> top
  let meet a b =
    match (a, b) with
    | (NegInf, other) -> other
    | (other, NegInf) -> other
    | (LB aa, LB bb) -> LB (Widening.max aa bb)
    | _ -> bot
  let zero = LB Int64.zero
  let leq a b = (join a b) = b
  let to_string (t : t) =
    match t with
    | NegInf -> "NegInf"
    | LB i -> "LB " ^ (Int64.to_string i)
    | Undef -> "Undef"
end
module LB = LowerBound (* Abbreviation *)

module ArrayLengthLowerBound =
struct
  type t =
    | PosInf
    | ALB of int64
    | Undef
  let (bot, top) = (Undef, PosInf)
  let join a b =
    match (a, b) with
    | (Undef, other) -> other
    | (other, Undef) -> other
    | (ALB aa, ALB bb) -> ALB (Widening.max aa bb)
    | _ -> top
  let meet a b =
    match (a, b) with
    | (PosInf, other) -> other
    | (other, PosInf) -> other
    | (ALB aa, ALB bb) -> ALB (Widening.min aa bb)
    | _ -> bot
  let to_string (t : t) =
    match t with
    | PosInf -> "+oo"
    | ALB i -> "ArrayLB " ^ (Int64.to_string i)
    | Undef -> "ArrayUndef"
end
module ALLB = ArrayLengthLowerBound

module ScalarConstraint =
struct
  type t = LB.t * UB.t (* Represents a half-open range *)
  let bot = (LB.bot, UB.bot)
  let top = (LB.NegInf, UB.PosInf)
  let join (alb, aub) (blb, bub) = (LB.join alb blb, UB.join aub bub)
  let meet (alb, aub) (blb, bub) = (LB.meet alb blb, UB.meet aub bub)
  let leq a b = (join a b) = b
  let of_int64 (i : int64) = (LB.LB i, UB.InclusiveUB (UB.IntAtom i))
  let of_int32 i = of_int64 (Int64.of_int32 i)
  let of_nativeint i = of_int64 (Int64.of_nativeint i)
  let of_int i = of_int64 (Int64.of_int i)
  let to_string (lb, ub) = "(" ^ (LB.to_string lb) ^ ", " ^ (UB.to_string ub) ^ ")"
end
module SC = ScalarConstraint

let rec zipEq (l1, l2) =
  match (l1, l2) with
  | (a :: l1', b :: l2') -> (a, b) :: (zipEq (l1', l2'))
  | _ -> raise Impossible

(* TODO: Fix uses of add to join? *)
module Lattice =
struct
  module VarMap =
  struct
    include Variable.Map
    let addOption k v map =
      match v with
      | Some v -> add k v map
      | None -> map
    (* runs in time proportional to size of map2.
     * Elements of map2 get added in case of conflict. *)
    let mergeVarMaps map1 map2 =
      let addFn key v lattice =
        Variable.Map.add key v (Variable.Map.remove key lattice) in
      Variable.Map.fold addFn map2 map1
  end
  module SymMap =
  struct
    include Symbol.Map
  end
  (* Sinan: It's annoying that we can't enforce that the varInfo in the
   * symMap is always a SymInfo on the type level. Since a variable can be
   * bound to a symbol and read at a later time, we need to include SymInfo
   * as a constructor for varInfo. *)
  type t = (varInfo VarMap.t) * (varInfo SymMap.t)
  and varInfo =
    | BoolInfo of boolConstraints
    | ScalarInfo of ScalarConstraint.t
    | ArrayOfLength of ALLB.t
    | NoInfo
    | SymInfo of varInfo list
  and boolConstraints = { ifTrue: varInfo VarMap.t; ifFalse: varInfo VarMap.t; }
  (* boolConstraints is a Map from variable value to constraints *)

  let bot = (VarMap.empty, SymMap.empty)
  (* Top doesn't exist, we don't know what the universe of keys is *)
  let rec bool_constraint_to_string {ifTrue; ifFalse} =
    "{ ifTrue: " ^ (var_map_to_string ifTrue) ^ "\n ifFalse: " ^ (var_map_to_string ifFalse) ^ "}"
  and var_info_to_string (vi : varInfo) =
    match vi with
    | BoolInfo bc -> "BoolInfo(" ^ (bool_constraint_to_string bc) ^ ")"
    | ScalarInfo sc -> "ScalarInfo(" ^ (ScalarConstraint.to_string sc) ^ ")"
    | ArrayOfLength sc -> "ArrayOfLength(" ^ (ALLB.to_string sc) ^ ")"
    | NoInfo -> "NoInfo"
    | SymInfo vis -> listToString "SymInfo" (List.map var_info_to_string vis)
  and var_map_to_string varMap =
    let bindings = VarMap.bindings varMap in
    let strFn (k, v) = ((Variable.unique_name k) ^ ": " ^ var_info_to_string v) ^ "\n" in
    listToString "Variable bindings: " (List.map strFn bindings)
  and to_string ((varMap, symMap) : t) =
    let bindings = SymMap.bindings symMap in
    let strFn (k, v) = ((Linkage_name.to_string (Symbol.label k))
                        ^ ": " ^ var_info_to_string v) ^ "\n" in
    let varDisplay = var_map_to_string varMap in
    let symDisplay = listToString "\nSymbol bindings: " (List.map strFn bindings) in
    varDisplay ^ symDisplay ^ "\n"

  let rec join (a, aSym) (b, bSym) =
    (joinVarMap a b, joinSymMap aSym bSym)
  and joinSymMap a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (joinVarInfo aa bb)
      | (Some _, None) -> a
      | (None, Some _) -> b
      | (None, None) -> raise Impossible
    in (joinVarMap a b, SymMap.merge f aSym bSym)
  and joinVarMap a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (joinVarInfo aa bb)
      | (Some _, None) -> a
      | (None, Some _) -> b
      | (None, None) -> raise Impossible
    in VarMap.merge f a b
  and joinVarInfo a b =
    match (a, b) with
    | (NoInfo, other) -> other
    | (other, NoInfo) -> other
    | (BoolInfo aa, BoolInfo bb) ->
      BoolInfo {
        ifTrue = joinVarMap aa.ifTrue bb.ifTrue;
        ifFalse = joinVarMap aa.ifFalse bb.ifFalse;
      }
    | (ScalarInfo aa, ScalarInfo bb) ->
      ScalarInfo (SC.join aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) ->
      ArrayOfLength (ALLB.join aa bb)
    | (SymInfo a, SymInfo b) ->
       SymInfo (List.map (fun (a, b) -> joinVarInfo a b) (zipEq (a, b)))
    | _ -> raise TypeMismatch

  let rec meet (aVar, aSym) (bVar, bSym) =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (meetVarInfo aa bb)
      | (Some _, None) -> a
      | (None, Some _) -> b
      | (None, None) -> raise Impossible
    in (meetVarInfo aVar bVar, SymMap.merge f aSym bSym)
  and meetVarMap a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (meetVarInfo aa bb)
      | (Some _, None) -> a
      | (None, Some _) -> b
      | (None, None) -> raise Impossible
    in VarMap.merge f a b
  and meetVarInfo a b =
    match (a, b) with
    | (NoInfo, _) -> NoInfo
    | (_, NoInfo) -> NoInfo
    | (BoolInfo aa, BoolInfo bb) ->
      BoolInfo {
        ifTrue = meetVarMap aa.ifTrue bb.ifTrue;
        ifFalse = meetVarMap aa.ifFalse bb.ifFalse;
      }
    | (ScalarInfo aa, ScalarInfo bb) ->
      ScalarInfo (SC.meet aa bb)
    | (SymInfo a, SymInfo b) ->
       SymInfo (List.map (fun (a, b) -> meetVarInfo a b) (zipEq (a, b)))
    | (ArrayOfLength aa, ArrayOfLength bb) ->
       ArrayOfLength (ALLB.meet aa bb)
    | _ -> raise TypeMismatch

  (* TODO: this is not correct since we have Other = _|_ *)
  let leq a b = join a b = b

  let getSymOpt ((_, symLattice) : t) (sym : Symbol.t) =
    if SymMap.mem sym symLattice
    then Some (SymMap.find sym symLattice)
    else None
  let getVarOpt ((varLattice, _) : t) (var : Variable.t) =
    if VarMap.mem var varLattice
    then Some (VarMap.find var varLattice)
    else None
  let getVar sigma x =
    match getVarOpt sigma x with
    | Some x -> x
    | None -> NoInfo
  let addVarInfo var info (varMap, symMap) = (VarMap.add var info varMap, symMap)
  let addSymInfo sym info (varMap, symMap) = (varMap, SymMap.add sym info symMap)
end
