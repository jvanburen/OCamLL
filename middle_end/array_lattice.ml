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

(*
  An issue with bool constraints containing non-constant variables
  is if we have a program such as
    b = x < y;
    x = x + 1;
    if x then ... else ...
  Then our boolean information is invalidated,
  so we can only keep immutable information in the bool constraints.

  A SOLUTION: when considering a expression of x < y, look up
  x' = sigma(x) and y' = sigma(y). The values in the lattice are constant and
  safe to propagate across assignment statements.
  This requires more complicated logic to deduce facts rather than just taking
  the meet of corresponding ranges, but that seems like a small price to pay
  for respecting mutables.
*)
exception Impossible of string
exception TypeMismatch


let listToString header (list : string list) = header ^ "[" ^ (String.concat ", " list) ^ "]"


(* TODO: implement widening operator
   raise an exception maybe and handle it in meet/join?*)
module Widening =
struct
  let min x y = Pervasives.min x y
  let max x y = Pervasives.max x y
end

(* Lattice Keys (symbol fields or variables) *)
(* This cleans up our immutable variable analysis considerably.
   The next step would be to add mutable variables.
   A major problem with this is that we don't distinguish at all between mutable and immutable variables.
   Such a problem will certainly confuse efforts later when we have code that modifies globals
*)
module Key =
struct
  type t =
    | Var of Variable.t
    | SymField of Symbol.t * int
    | Zero  (* This is for constants *)

  include Identifiable.Make (struct
    type nonrec t = t
    let compare e1 e2 =
      if e1 == e2 then 0
      else match (e1, e2) with
        | (Zero, Zero) -> 0
        | (Zero, _) -> -1
        | (_, Zero) -> 1
        | (Var x, Var y) -> Variable.compare x y
        | (Var _, _) -> -1
        | (_, Var _) -> 1
        | (SymField (s1, i1), SymField (s2, i2)) ->
          if i1 <> i2 then i1 - i2
          else Symbol.compare s1 s2


    let equal x y = (x == y) || (compare x y = 0)
    let output chan t = match t with
      | Var v -> Variable.output chan v
      | SymField (sym, i) ->
          (Symbol.output chan sym; output_string chan (string_of_int i))
      | Zero -> output_string chan "Zero"
    let hash t = match t with
      | Var v -> Variable.hash v
      | SymField (sym, i) -> Symbol.hash sym lxor (i + (i lsl 16))
      | Zero -> 0
    let print ppf t = match t with
      | Var v -> Variable.print ppf v
      | Zero -> Format.pp_print_string ppf "Zero"
      | SymField (sym, i) -> (
          Symbol.print ppf sym;
          Format.pp_print_string ppf ("(" ^ string_of_int i ^ ")")
        )
  end)

  let of_sym (sym, i) = (SymField (sym, i))
  let of_var var = (Var var)
end
module K = Key

module type LatticeOps =
sig
  val joinOffsets : Key.t -> int64 -> int64 -> int64 option
  val meetOffsets : Key.t -> int64 -> int64 -> int64 option
end
module KeyLattice (Ops : LatticeOps) =
struct
  (* For upper bounds:
  We keep a map of multiple upper bounds
  k -> v means we're bounded above by k + v
  if a key is not in the map it's equivalent to k -> +oo.
  Hence Top for this lattice is the empty map, i.e., we're bounded above by nothing
  We don't have an explicit _|_ because this will be a value in a map,
      where the absence of a value is a _|_
  *)
  type t = int64 Key.Map.t (* offsets *)
  let top = Key.Map.empty

  (* Move higher in the lattice (towards Top) *)
  let join a b =
    let f k x y = match (x, y) with
      | (Some x, Some y) -> Ops.joinOffsets k x y
      | (None, _) -> None
      | (_, None) -> None
    in Key.Map.merge f a b
  let meet a b =
    let f k x y = match (x, y) with
      | (Some x, Some y) -> Ops.meetOffsets k x y
      | (None, other) -> other
      | (other, None) -> other
    in Key.Map.merge f a b
  let leq a b = (join a b) = b (* TODO-someday: make this more efficient *)
  let plus_constant (c : int64) (lat : t) : t = Key.Map.map (Int64.add c) lat

  let of_offset k v : t = Key.Map.singleton k v
  let of_key k : t = Key.Map.singleton k Int64.zero
  let of_int64 v : t = of_offset Key.Zero v
  let of_var v : t = of_key (Key.of_var v)
end

module UpperBound = KeyLattice(struct
  let joinOffsets _ x y = Some (Widening.max x y)
  let meetOffsets _ x y = Some (Widening.min x y)
end) module UB = UpperBound

module LowerBound = KeyLattice(struct
  let joinOffsets _ x y = Some (Widening.min x y)
  let meetOffsets _ x y = Some (Widening.max x y)
end) module LB = LowerBound

type scalarConstraint = {lb: LB.t; ub: UB.t} (* Ranges are inclusive *)
module ScalarConstraint =
struct
  type t = scalarConstraint
  let top = {lb = LB.top; ub = UB.top}
  let join a b = {lb = LB.join a.lb b.lb; ub = UB.join a.ub b.ub}
  let meet a b = {lb = LB.meet a.lb b.lb; ub = UB.meet a.ub b.ub}
  let leq a b = (LB.leq a.lb b.lb && UB.leq a.ub b.ub)

  let plus_constant (c : int64) (sc : t) : t =
    {lb = LB.plus_constant c sc.lb;
     ub = UB.plus_constant c sc.ub}

  let of_int64 (i : int64) : t = {lb = LB.of_int64 i; ub = UB.of_int64 i}
  let of_int32 i : t = of_int64 (Int64.of_int32 i)
  let of_nativeint i : t = of_int64 (Int64.of_nativeint i)
  let of_int i : t = of_int64 (Int64.of_int i)
  let of_key k : t = {lb = LB.of_key k; ub = UB.of_key k}
  let of_var v : t = of_key (Key.of_var v)

  let of_upper_bound ub : t = {lb=LB.top; ub=ub}
  let of_lower_bound lb : t = {lb=lb; ub=UB.top}
  let nonnegative : t = of_lower_bound (LB.of_int64 Int64.zero)

  let print ppf (sc : t) : unit =
    let open Format in
    let print_entry k x y = (
      pp_open_hbox ppf ();
      pp_print_string ppf "(";
      Key.print ppf k;
      pp_print_string ppf " +";
      pp_print_space ppf ();
      pp_open_hbox ppf ();
      pp_print_string ppf (match x with
                          | Some x ->  ("[" ^ Int64.to_string x ^ ",")
                          | None -> "(-oo,"
                          );
      pp_print_space ppf ();
      pp_print_string ppf (match y with
                          | Some y -> (Int64.to_string y ^ "]")
                          | None -> "+oo)"
                          );
      pp_close_box ppf ();
      pp_print_string ppf ")";
      pp_close_box ppf ();
      pp_print_space ppf ();
      None (* We're using the merge function, so whatever *)
    ) in (
      pp_open_hvbox ppf 2;
      pp_print_string ppf "ScalarConstraints{";
      pp_print_space ppf ();
      ignore (Key.Map.merge print_entry sc.lb sc.ub);
      pp_print_cut ppf ();
      pp_print_string ppf "}";
      pp_close_box ppf ()
    )
end module SC = ScalarConstraint

type 'a keyMap = 'a Key.Map.t
type lattice = latticeVarInfo keyMap
and latticeVarInfo =
  | BoolInfo of boolConstraints
  | ScalarInfo of ScalarConstraint.t
  | ArrayOfLength of ScalarConstraint.t (* Jacob TODO-now: Collapse this w/ ScalarInfo? Might add logic errors to do so. *)
  | Anything (* Top, used when we can't analyze something at all *)
and boolConstraints = { ifTrue: lattice; ifFalse: lattice; }
(* boolConstraints is a Map from variable value to constraints *)

module Lattice =
struct
  module KeyMap = Key.Map
  type t = lattice
  type varInfo = latticeVarInfo

  let bot = KeyMap.empty (* Initial value for analysis woohoo *)
  (* Top is never used explicitly *)
  let rec print ppf (lattice : t) : unit = begin
    let open Format in
    let print_entry k x = (
      pp_open_hvbox ppf 2;
      pp_print_string ppf "(";
      Key.print ppf k;
      pp_print_string ppf ":";
      pp_print_space ppf ();
      (match x with
      | Anything -> pp_print_string ppf "Top"
      | BoolInfo boolInfo -> (
          pp_open_hvbox ppf 2;
          pp_print_string ppf "BoolInfo{";
          pp_print_cut ppf ();
          pp_print_string ppf "T->";
          pp_print_break ppf 1 3;
          print ppf boolInfo.ifTrue;
          pp_print_space ppf ();
          pp_print_string ppf "F->";
          pp_print_break ppf 1 3;
          print ppf boolInfo.ifFalse;
          pp_close_box ppf () )
      | ScalarInfo sc -> SC.print ppf sc
      | ArrayOfLength sc -> (pp_open_hbox ppf ();
                             pp_print_string ppf "ArrayOfLength";
                             pp_print_space ppf ();
                             SC.print ppf sc;
                             pp_close_box ppf () )
      );
      pp_print_string ppf ")";
      pp_close_box ppf ();
      pp_print_cut ppf ()
    ) in (
      pp_open_vbox ppf 2;
      pp_print_string ppf "Lattice:{";
      pp_print_space ppf ();
      KeyMap.iter print_entry lattice;
      pp_print_string ppf "}";
      pp_close_box ppf () )
    end

  let dump (sigma : t) : unit = (
    Format.pp_print_flush Format.std_formatter ();
    print (Format.std_formatter) sigma;
    Format.pp_print_flush Format.std_formatter ();
    print_newline ();)

  let rec join a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (joinVarInfo aa bb)
      | (Some _, None) -> a (* Remember that None -> _|_ *)
      | (None, Some _) -> b (* and we want to join towards top *)
      | (None, None) -> (* None *) raise (Impossible "Lattice.join.f")
    in KeyMap.merge f a b
  and joinVarInfo a b =
    match (a, b) with
    | (Anything, _) -> Anything
    | (_, Anything) -> Anything
    | (BoolInfo aa, BoolInfo bb) -> BoolInfo {
                                      ifTrue = join aa.ifTrue bb.ifTrue;
                                      ifFalse = join aa.ifFalse bb.ifFalse;
                                    }
    | (ScalarInfo aa, ScalarInfo bb) -> ScalarInfo (SC.join aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) -> ArrayOfLength (SC.join aa bb)
    | _ -> raise TypeMismatch

  let rec meet a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (meetVarInfo aa bb)
      | (Some _, None) -> None (* meet towards _|_ *)
      | (None, Some _) -> None (* TODO: empirically verify this *)
      | (None, None) -> (* None *) raise (Impossible "Lattice.meet.f")
    in KeyMap.merge f a b
  and meetVarInfo a b =
    match (a, b) with
    | (Anything, other) -> other
    | (other, Anything) -> other
    | (BoolInfo aa, BoolInfo bb) -> BoolInfo {
                                      ifTrue = meet aa.ifTrue bb.ifTrue;
                                      ifFalse = meet aa.ifFalse bb.ifFalse;
                                    }
    | (ScalarInfo aa, ScalarInfo bb) -> ScalarInfo (SC.meet aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) -> ArrayOfLength (SC.meet aa bb)
    | _ -> raise TypeMismatch


  (* TODO: leq is not correct since we have Other = _|_ *)
  (* let leq a b = join a b = b *)

  let getKey_exn k sigma = KeyMap.find k sigma

  let getKey_opt k sigma =
    try Some (getKey_exn k sigma)
    with Not_found -> None

  let getVar_top v sigma =
    match getKey_opt (K.of_var v) sigma with
    | Some x -> x
    | None -> Anything

  let getSymField_top sym sigma =
    match getKey_opt (K.of_sym sym) sigma with
    | Some x -> x
    | None -> Anything

  let updateKey k info sigma = KeyMap.add k info (KeyMap.remove k sigma)
  let updateVar var info sigma = updateKey (Key.of_var var) info sigma
  let updateSymField sym field info sigma = updateKey (Key.of_sym (sym, field)) info sigma
  let singleton key info : t = KeyMap.singleton key info
  let of_list l : t = KeyMap.of_list l

  let rec combineVarInfo_shallow (v1 : varInfo) (v2 : varInfo) : varInfo =
    match (v1, v2) with
    | (Anything, other) -> other
    | (other, Anything) -> other
    | (BoolInfo aa, BoolInfo bb) ->
        BoolInfo {
          ifTrue = combineLattices_shallow aa.ifTrue bb.ifTrue;
          ifFalse = combineLattices_shallow aa.ifFalse bb.ifFalse;
        }
    | (ScalarInfo aa, ScalarInfo bb) -> ScalarInfo (SC.meet aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) -> ArrayOfLength (SC.meet aa bb)
    | _ -> raise TypeMismatch
  and combineLattices_shallow (s1 : t) (s2 : t) : t =
    KeyMap.union_merge combineVarInfo_shallow s1 s2

  (* refines bindings in second with info from first *)
  (* let refineLatticeWith (first : t) (second : t) : t =
    let mergeRight x y =
      match (x, y) with
      | (Some x, Some y) -> Some (meetVarInfo x y)
      | (None, Some y) -> Some y
      | (_, None) -> None
    in
    KeyMap.merge mergeRight first second *)

  let computeClosure (sigma : t) : t =
    let addReverseRangeToSC ((lb, ub): int64 option * int64 option)
                        (sc : SC.t) : SC.t =
      (* adds, then join. yes, we're intentionally flipping lb and ub *)
      {lb=(match ub with
          | Some ub -> LB.plus_constant (Int64.neg ub) sc.lb
          | None -> LB.top);
       ub=(match lb with
          | Some lb -> UB.plus_constant (Int64.neg lb) sc.ub
          | None -> UB.top)
      }
    in
    let getSCLattice (sc : SC.t) : t =
      (* Takes a key -> SC mapping and turns it into a lattice of additional constraints *)
      (* it promotes a scalarconstraint to a lattice *)
      let f x lb ub =
        (* turns a single constraint x -> [xlo, xhi] into a scalarconstraint *)
        if x = Key.Zero then None
        else Some (ScalarInfo (addReverseRangeToSC (lb, ub) sc))
      in
      KeyMap.merge f sc.lb sc.ub
    in
    let accumVarInfo (_ : Key.t) (v : varInfo) (acc : t) : t =
      match v with
      | ScalarInfo sc
      | ArrayOfLength sc ->
        combineLattices_shallow (getSCLattice sc) acc
      | _ -> acc (* probably no need to go into it this far... *)
    in
    KeyMap.fold accumVarInfo sigma sigma

  let addFreeVars (vars : Variable.Set.t) (sigma : t) : t =
    let addvar var s =
      KeyMap.add (Key.of_var var) (ScalarInfo (SC.of_var var)) s
    in
      Variable.Set.fold addvar vars sigma

  let fmapBoolConstraints (f : t -> t)
                          (boolInfo : boolConstraints) : boolConstraints =
    { ifTrue = f boolInfo.ifTrue; ifFalse = f boolInfo.ifFalse; }


  let debug_println s =
    (Format.pp_print_flush Format.std_formatter ();
    print_string s;
    print_newline ();
    Format.pp_print_flush Format.std_formatter ();)

  let applyBoolInfo (boolInfo : boolConstraints) (sigma : t) : boolConstraints =
    let result =
      fmapBoolConstraints computeClosure
      { ifTrue = combineLattices_shallow sigma boolInfo.ifTrue;
        ifFalse = combineLattices_shallow sigma boolInfo.ifFalse;
      } in
    (debug_println "applying bool info to lattice:";
     dump sigma;
     debug_println "True branch after:";
     dump (result.ifTrue);
     result
    )

  let computeBoolInfo (k : Key.t) (sigma : t) : boolConstraints =
    match getKey_opt k sigma with
    | Some (BoolInfo boolInfo) -> applyBoolInfo boolInfo sigma
    | _ -> { ifTrue = sigma; ifFalse = sigma; }


end
module L = Lattice

(* Don't know how to implement this yet.
   This is a simple abstract interface allowing me to fix up array_optis
   before we deal with it *)
module ProgramLattices =
struct
  type t = unit
  let initial = ()
  let updateOut (_ : t)
                (_ : Flambda.t)
                (lat: Lattice.t) = lat
  (* Idea: let statements could be identified by the variable they define *)
end module LL = ProgramLattices
