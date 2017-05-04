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

let pass_name = "analyze-array-accesses"
let () = Pass_wrapper.register ~pass_name:pass_name

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
    | VarAtom of Variable.t
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
    | (VarAtom x, VarAtom y) -> if x = y then s a else k ()
    | _ -> k ()

  let join a b =
    match (a, b) with
    | (Undef, other) -> other
    | (other, Undef) -> other
    | (UB aa, UB bb) -> atomOp Widening.max (fun x -> UB x) (fun () -> top) aa bb
    | (InclusiveUB aa, InclusiveUB bb) ->
       atomOp Widening.max (fun x -> UB x) (fun () -> top) aa bb
    | _ -> top
  let meet a b =
    match (a, b) with
    | (PosInf, other) -> other
    | (other, PosInf) -> other
    | (UB aa, UB bb) -> atomOp Widening.min (fun x -> UB x) (fun () -> bot) aa bb
    | (InclusiveUB aa, InclusiveUB bb) ->
       atomOp Widening.min (fun x -> UB x) (fun () -> bot) aa bb
    | _ -> bot
  let leq a b = (join a b) = b
  let atom_to_string atom =
    match atom with
    | LenAtom var -> "LenAtom " ^ (Variable.unique_name var)
    | VarAtom var -> "VarAtom " ^ (Variable.unique_name var)
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


module ScalarConstraint =
struct
  type t = LB.t * UB.t (* Represents a half-open range *)
  let bot = (LB.bot, UB.bot)
  let top = (LB.NegInf, UB.PosInf)
  let join (alb, aub) (blb, bub) = (LB.join alb blb, UB.join aub bub)
  let meet (alb, aub) (blb, bub) = (LB.meet alb blb, UB.meet aub bub)
  let leq a b = (join a b) = b
  let of_int64 (i : int64) = (LB.LB i, UB.UB (UB.IntAtom (Int64.succ i)))
  let of_int32 i = of_int64 (Int64.of_int32 i)
  let of_nativeint i = of_int64 (Int64.of_nativeint i)
  let of_int i = of_int64 (Int64.of_int i)
  let to_string (lb, ub) = "(" ^ (LB.to_string lb) ^ ", " ^ (UB.to_string ub) ^ ")"
end
module SC = ScalarConstraint

let rec zip (l1, l2) =
  match (l1, l2) with
  | ([], _) -> []
  | (_, []) -> []
  | (a :: l1', b :: l2') -> (a, b) :: (zip (l1', l2'))
              
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
    | (SymInfo a, SymInfo b) ->
       SymInfo (List.map (fun (a, b) -> joinVarInfo a b) (zip (a, b)))
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
       SymInfo (List.map (fun (a, b) -> meetVarInfo a b) (zip (a, b)))
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
  let addVarInfo var info (varMap, symMap) = (VarMap.add var info varMap, symMap)
  let addSymInfo sym info (varMap, symMap) = (varMap, SymMap.add sym info symMap)
end

exception No_value
let option_get opt =
  match opt with
  | Some x -> x
  | None -> raise No_value

let getVarInfo (var : Variable.t) ((map, _) : Lattice.t) =
  Lattice.VarMap.find var map

let get_comparison_info (known : Lattice.t)
                        (comparison : Lambda.comparison)
                        (left : Variable.t)
                        (right : Variable.t) =
  let mapFromTwo (k1, v1) (k2, v2) =
    Lattice.VarMap.add k1 v1 (Lattice.VarMap.singleton k2 v2) in
  let getUBOpt var =
    match Lattice.getVarOpt known var  with
    | Some info ->
       (match info with
        | Lattice.ScalarInfo (_, ub) -> Some ub
        | _ -> None)
    | None -> None in
  let getLBOpt var =
    match Lattice.getVarOpt known var with
    | Some info ->
       (match info with
        | Lattice.ScalarInfo (lb, _) -> Some lb
        | _ -> None)
    | None -> None in
  let ltConstraint a b =
    match (getLBOpt a, getUBOpt a, getUBOpt b) with
    | _ -> Lattice.NoInfo in
  let lteConstraint _ var = Lattice.ScalarInfo (LB.NegInf, UB.InclusiveUB (UB.VarAtom var)) in
  (* TODO: implement these correctly. *)
  let gtConstraint _ _ = Lattice.ScalarInfo (LB.NegInf, UB.PosInf) in
  let gteConstraint _ _ = Lattice.ScalarInfo (LB.NegInf, UB.PosInf) in
  let eqConstraint _ _ = Lattice.ScalarInfo (LB.NegInf, UB.PosInf) in
  let neqConstraint _ _ = Lattice.ScalarInfo (LB.NegInf, UB.PosInf) in
  match comparison with
  | Lambda.Clt -> {Lattice.ifTrue = mapFromTwo (left, ltConstraint left right)
                                               (right, gtConstraint right left);
                   Lattice.ifFalse = mapFromTwo (left, gteConstraint left right)
                                                (right, lteConstraint right left)}
                    
  | Lambda.Cgt -> {Lattice.ifTrue = mapFromTwo (left, gtConstraint left right)
                                               (right, ltConstraint right left);
                   Lattice.ifFalse = mapFromTwo (left, lteConstraint left right)
                                                (right, gteConstraint right left)}
                    
  | Lambda.Cle -> {Lattice.ifTrue = mapFromTwo (left, lteConstraint left right)
                                                (right, gteConstraint right left);
                    Lattice.ifFalse = mapFromTwo (left, gtConstraint left right)
                                                 (right, ltConstraint right left)}
                     
  | Lambda.Cge -> {Lattice.ifTrue = mapFromTwo (left, gteConstraint left right)
                                                (right, lteConstraint right left);
                    Lattice.ifFalse = mapFromTwo (left, ltConstraint left right)
                                                 (right, gtConstraint right left)}
                     
  | Lambda.Ceq -> {Lattice.ifTrue = mapFromTwo (left, eqConstraint left right)
                                                (right, eqConstraint right left);
                    Lattice.ifFalse = mapFromTwo (left, neqConstraint left right)
                                                 (right, neqConstraint right left)}
                     
  | Lambda.Cneq -> {Lattice.ifTrue = mapFromTwo (left, neqConstraint left right)
                                                (right, neqConstraint right left);
                    Lattice.ifFalse = mapFromTwo (left, eqConstraint left right)
                                                 (right, eqConstraint right left)}

                     
                     
let rec add_constraints (known : Lattice.t) (flam : Flambda.t) : (Lattice.t * Lattice.varInfo) =
  match flam with
  | Flambda.Var v -> (known, getVarInfo v known)
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body; _} ->
    let _ = print_string ("In a let with variable " ^ (Variable.unique_name var) ^ "\n") in 
    let _ = if Variable.unique_name var = "match_32" then
              Flambda.print_named Format.std_formatter defining_expr
            else () in
    let (known, deInfo) = add_constraints_named known defining_expr in
    let known = Lattice.addVarInfo var deInfo known in
    add_constraints known body
  (* Right now, we ignore mutable variables. no memory woohoo *)
  | Flambda.Let_mutable {Flambda.body; _} -> add_constraints known body
  | Flambda.Let_rec (defs, body) ->
    let add_def known (name, def) =
      let (known, defInfo) = add_constraints_named known def
      in (Lattice.addVarInfo name defInfo known) in
    let known = List.fold_left add_def known defs in
     add_constraints known body
  (* We don't known anything about functions right now, although maybe we ought to.
   * Note that in flambda, apply is var(var, var, ...) so we can't gleam any more info
   * by traversing. *)
  | Flambda.Apply _ -> (known, Lattice.NoInfo)
  (* Object oriented stuff, ew *)
  | Flambda.Send _ -> (known, Lattice.NoInfo)
  (* Assignment of a mutable variable. We might want to return to this later *)
  | Flambda.Assign _ -> (known, Lattice.NoInfo)
  | Flambda.If_then_else (_, trueBranch, falseBranch) ->
    (* TODO: Do we need to add the iftrue/iffalse information in some fashion
     * while analyzing the branches?
     * Jacob: yes *)
    let (sigmaTrue, trueInfo) = add_constraints known trueBranch in
    let (sigmaFalse, falseInfo) = add_constraints known falseBranch in
    let sigmaBoth = Lattice.join sigmaTrue sigmaFalse in
    let sigmaNew = Lattice.join known sigmaBoth in
    (sigmaNew, Lattice.joinVarInfo trueInfo falseInfo)
  | Flambda.Switch (_, {Flambda.consts; Flambda.blocks; Flambda.failaction}) ->
    let add_case (known, possibleInfos) (_, case) =
      let (known2, caseInfo) = add_constraints known case
      in (Lattice.join known known2, caseInfo :: possibleInfos)
    in
    let (known, possibleInfos) = List.fold_left add_case (known, []) consts in
    let (known, possibleInfos) = List.fold_left add_case (known, possibleInfos) blocks in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Lattice.NoInfo in
    begin match failaction with
     | None -> (known, switchInfo)
     | Some action -> let (known, actionInfo) = add_constraints known action in
                      (known, Lattice.joinVarInfo switchInfo actionInfo)
    end
  | Flambda.String_switch (_, cases, fallthrough) ->
    let add_case (known, possibleInfos) (_, case) =
      let (known2, caseInfo) = add_constraints known case
      in (Lattice.join known known2, caseInfo :: possibleInfos) in
    let (known, possibleInfos) = List.fold_left add_case (known, []) cases in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Lattice.NoInfo in
    begin match fallthrough with
     | None -> (known, switchInfo)
     | Some action -> let (known, actionInfo) = add_constraints known action in
                      (known, Lattice.joinVarInfo switchInfo actionInfo)
    end
  | Flambda.Try_with (exp, _, handler) ->
    let (known, expInfo) = add_constraints known exp in
    let (known, handlerInfo) = add_constraints known handler in
    (known, Lattice.joinVarInfo expInfo handlerInfo)
  | Flambda.While (cond, body) ->
    let (known, _) = add_constraints known cond in
    let (known, _) = add_constraints known body in
    (* In general, we can't know anything about a while loop because who knows if the
     * condition will ever be true *)
    (known, Lattice.NoInfo)
  | Flambda.For { Flambda.body; _; } -> add_constraints known body
  | Flambda.Proved_unreachable -> (known, Lattice.NoInfo)
  | _ -> (known, Lattice.NoInfo)
and add_constraints_named (known : Lattice.t) (named : Flambda.named) : (Lattice.t * Lattice.varInfo) =
  match named with
  (* Symbols are handles for constants from seperate compilation units. We might need to check
   * for arraylength or something here. *)
  | Flambda.Symbol sym ->
     (known, (match Lattice.getSymOpt known sym with
              | Some vi -> vi
              | None -> Lattice.NoInfo))
  | Flambda.Const c -> (known, (match c with
                                | Flambda.Int i -> Lattice.ScalarInfo (SC.of_int i)
                                | Flambda.Char _ -> Lattice.NoInfo
                                | Flambda.Const_pointer _ -> Lattice.NoInfo))
  | Flambda.Allocated_const c ->
    (known, match c with
            | Allocated_const.Int32 i -> Lattice.ScalarInfo (SC.of_int32 i)
            | Allocated_const.Int64 i -> Lattice.ScalarInfo (SC.of_int64 i)
            | Allocated_const.Nativeint ni -> Lattice.ScalarInfo (SC.of_nativeint ni)
            | Allocated_const.Float _
              | Allocated_const.String _
              | Allocated_const.Float_array _
              | Allocated_const.Immutable_string _
              | Allocated_const.Immutable_float_array _ -> Lattice.NoInfo
    )
  | Flambda.Read_mutable _ -> (known, Lattice.NoInfo)
  (* Once again, symbols might be useful to look at later. *)
  | Flambda.Read_symbol_field (sym, idx) ->
     let fieldInfo =
       (match Lattice.getSymOpt known sym with
        | Some (Lattice.SymInfo fieldInfoList) -> List.nth fieldInfoList idx
        | _ -> Lattice.NoInfo) in
     (known, fieldInfo)
  | Flambda.Set_of_closures {Flambda.function_decls = {Flambda.funs; _}; _} ->
     let bindings = Variable.Map.bindings funs in
     let addBindings known (_, ({Flambda.body;} : Flambda.function_declaration)) =
       let (known2, _) = add_constraints known body in known2 in
     (List.fold_left addBindings known bindings, Lattice.NoInfo)
  | Flambda.Prim (prim, vars, _) ->
      let info = match (prim, vars) with
       (* Ensure we're only looking at the length of a single array. *)
       | (Lambda.Parraylength _, [var]) ->
          Lattice.ScalarInfo (LB.zero, UB.UB (UB.LenAtom var))
       | (Lambda.Pintcomp comparison, left :: right :: []) ->
         Lattice.BoolInfo (get_comparison_info known comparison left right)
       | _ -> Lattice.NoInfo
      in (known, info)
  | Flambda.Expr expr -> add_constraints known expr
  | _ -> (known, Lattice.NoInfo)
