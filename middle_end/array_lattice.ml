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

exception Impossible of string
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

(* Lattice Keys (symbol fields or variables) *)
module Key =
struct
  type t =
    | Var of Variable.t
    | SymField of Symbol.t * int
    | Zero  (* This is for constants *)

  include Identifiable.Make (struct
    type nonrec t = t
    let compare e1 e2 = match (e1, e2) with
        | (Zero, Zero) -> 0
        | (Zero, _) -> -1
        | (_, Zero) -> 1
        | (Var x, Var y) -> Variable.compare x y
        | (Var _, _) -> -1
        | (_, Var_ ) -> 1
        | (SymField (e1, i1), SymField (e2, i2)) ->
          if i1 = i2
            then Symbol.compare x y
            else Int.compare i1 i2

    let equal x y = (x == y) || (compare x y = 0)
    let output chan t = match t with
      | Var v -> Variable.output chan v
      | SymField (sym, i) ->
          (Symbol.output sym; output_string chan (string_of_int i))
      | Zero -> output_string chan "Zero"
    let hash t = match t with
      | Var v -> v.hash
      | SymField (sym, _) -> sym.hash
      | Zero -> 0
    let print ppf t = match t with
      | Var v -> Variable.print ppf v
      | Zero -> Format.pp_print_string ppf "Zero"
      | SymField (sym, i) -> (
          Symbol.print ppf sym;
          Format.pp_print_string ppf ("(" ^ string_of_int i ^ ")");
        )
  end)

  let of_sym (sym, i) = Sym sym i
  let of_var var = Var var
end
module K = Key

module type LatticeOps =
sig
  val joinTwo : Key.t -> int64 -> int64 -> int64 option
  val meetTwo : Key.t -> int64 -> int64 -> int64 option
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
      | (Some x, Some y) -> Ops.joinTwo k x y
      | (None, _) -> None
      | (_, None) -> None
    in Key.Map.merge f a b
  let meet a b =
    let f k x y = match (x, y) with
      | (Some x, Some y) -> Ops.meetTwo k x y
      | (None, other) -> other
      | (other, None) -> other
    in Key.Map.merge f a b
  let leq a b = (join a b) = b (* TODO-someday: make this more efficient *)

  let of_offset k (v : int64) = Key.Map.singleton k v
  let of_int64 v = of_offset Key.Zero v
end

module UpperBound = KeyLattice(struct
  let joinTwo _ = Widening.max
  let meetTwo _ = Widening.min
end) module UB = UpperBound

module LowerBound = KeyLattice(struct
  let joinTwo _ = Widening.min
  let meetTwo _ = Widening.max
end) module LB = LowerBound

module ScalarConstraint =
struct
  type t = {lb: LB.t; ub: UB.t} (* Ranges are inclusive *)
  let top = {lb = LB.top; ub = UB.top}
  let join a b = {lb = LB.join a.lb b.lb, ub = UB.join a.ub b.ub}
  let meet a b = {lb = LB.meet a.lb b.lb, ub = UB.meet a.ub b.ub}
  let leq a b = (LB.leq a.lb b.lb && UB.leq a.ub b.ub)

  let of_int64 (i : int64) = (LB.of_int64 i, UB.of_int64 i)
  let of_int32 i = of_int64 (Int64.of_int32 i)
  let of_nativeint i = of_int64 (Int64.of_nativeint i)
  let of_int i = of_int64 (Int64.of_int i)

  let print ppf ((lbs, ubs) : t) : unit =
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
                          )
      pp_print_space ppf ();
      pp_print_string ppf (match y with
                          | Some y -> (Int64.to_string y ^ "]")
                          | None -> "+oo)"
                          )
      pp_close_box ppf ();
      pp_print_string ppf ")";
      pp_close_box ppf ();
      pp_print_space ppf ();
      None (* We're using the merge function, so whatever *)
    ) in (
      pp_open_hvbox ppf 2;
      pp_print_string ppf "ScalarConstraints{"
      pp_print_space ppf ();
      ignore (Key.Map.merge print_entry lbs ubs);
      pp_print_cut ppf ();
      pp_print_string ppf "}";
      pp_close_box ppf ()
    )
end module SC = ScalarConstraint

(* let rec zipEq (l1, l2) =
  match (l1, l2) with
  | (a :: l1', b :: l2') -> (a, b) :: (zipEq (l1', l2'))
  | ([], []) -> []
  | _ -> raise (Impossible "Zip") *)

module Lattice =
struct
  module KeyMap = Key.Map
  type 'a keyMap = 'a Key.Map.t
  type t = varInfo keyMap
  and varInfo =
    | BoolInfo of boolConstraints
    | ScalarInfo of ScalarConstraint.t
    | ArrayOfLength of ScalarConstraint.t (* Jacob TODO-now: Collapse this w/ ScalarInfo? Might add logic errors to do so. *)
    (*| NoInfo (* Jacob TODO-now: is this needed?? *)*)
  and boolConstraints = { ifTrue: t; ifFalse: t; }
  (* boolConstraints is a Map from variable value to constraints *)

  let bot = KeyMap.empty (* Initial value for analysis woohoo *)
  (* Top is never used explicitly *)
  let rec print ppf (lattice : t) : unit =
    let print_entry k x = begin
      pp_open_hvbox ppf 2;
      pp_print_string ppf "(";
      Key.print ppf k;
      pp_print_string ppf ":";
      pp_print_space ppf ();
      (match x with
      | BoolInfo boolInfo -> (
          pp_open_hvbox ppf 2;
          pp_print_string ppf "BoolInfo{";
          pp_print_cut ppf ();
          pp_print_string ppf "T->";
          pp_print_break ppf 1 3;
          print ppf boolInfo.ifTrue;
          pp_print_space ppf ();
          pp_print_string ppf "F->";
          pp_print_break 1 3 ();
          print ppf boolInfo.ifFalse;
          pp_close_box();
        )
      | ScalarInfo sc -> SC.print ppf sc
      | ArrayOfLength sc -> (pp_open_hbox ppf ();
                             pp_print_string ppf "ArrayOfLength";
                             pp_print_space ppf ();
                             SC.print ppf sc;
                             pp_close_box ppf ())
      (* | NoInfo -> pp_print_string ppf "_|_" *)
      );
      pp_print_string ppf ")";
      pp_close_box ppf ();
      pp_print_cut ppf ()
    end in
    begin
      pp_open_vbox ppf 2;
      pp_print_string ppf "Lattice:{"
      pp_print_space ppf ();
      KeyMap.iter print_entry lattice;
      pp_print_string ppf "}";
      pp_close_box ppf ()
    end

  let rec join a b =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (joinVarInfo aa bb)
      | (Some _, None) -> a (* Remember that None -> _|_ *)
      | (None, Some _) -> b (* and we want to join towards top *)
      | (None, None) -> (* None *) raise (Impossible "Lattice.join.f")
    in KeyMap.merge f a b
  and joinVarInfo a b =
    match (a, b) with (*
    | (NoInfo, other) -> other
    | (other, NoInfo) -> other*)
    | (BoolInfo aa, BoolInfo bb) -> BoolInfo {
                                      ifTrue = join aa.ifTrue bb.ifTrue;
                                      ifFalse = join aa.ifFalse bb.ifFalse;
                                    }
    | (ScalarInfo aa, ScalarInfo bb) -> ScalarInfo (SC.join aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) -> ArrayOfLength (ALLB.join aa bb)
    | _ -> raise TypeMismatch

  let rec meet a =
    let f _ a b =
      match (a, b) with
      | (Some aa, Some bb) -> Some (meetVarInfo aa bb)
      | (Some _, None) -> None (* meet towards _|_ *)
      | (None, Some _) -> None (* TODO: empirically verify this *)
      | (None, None) -> raise (Impossible "Lattice.meet.f")
    in KeyMap.merge f a b
  and meetVarInfo a b =
    match (a, b) with (*
    | (NoInfo, _) -> NoInfo
    | (_, NoInfo) -> NoInfo *)
    | (BoolInfo aa, BoolInfo bb) -> BoolInfo {
                                      ifTrue = meet aa.ifTrue bb.ifTrue;
                                      ifFalse = meet aa.ifFalse bb.ifFalse;
                                    }
    | (ScalarInfo aa, ScalarInfo bb) -> ScalarInfo (SC.meet aa bb)
    | (ArrayOfLength aa, ArrayOfLength bb) -> ArrayOfLength (ALLB.meet aa bb)
    | _ -> raise TypeMismatch


  (* TODO: this is not correct since we have Other = _|_ *)
  (* let leq a b = join a b = b *)
(*
  let getSymOpt ((_, symLattice) : t) (sym : Symbol.t) =
    if SymMap.mem sym symLattice
    then Some (SymMap.find sym symLattice)
    else None *)
  (* let getVarOpt ((varLattice, _) : t) (var : Variable.t) =
    if VarMap.mem var varLattice
    then Some (VarMap.find var varLattice)
    else None *)
  let getKey sigma k =
    try Some (VarMap.find sigma k)
    with Not_found -> None

  let getkey_exn sigma k = VarMap.find sigma k
  (* let addVarInfo var info (varMap, symMap) = (VarMap.add var info varMap, symMap) *)
  (* let addSymInfo sym info (varMap, symMap) = (varMap, SymMap.add sym info symMap) *)

  let applyBoolInfo (sigma : t) (boolInfo : boolConstraints) : boolConstraints =
    { ifTrue = meet sigma boolInfo.ifTrue;
      ifFalse = meet sigma boolInfo.ifFalse;
    }
end
