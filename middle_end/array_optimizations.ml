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

let pass_name = "analyze-array-accesses"
let () = Pass_wrapper.register ~pass_name:pass_name

open Array_lattice

(* let getVarInfo (var : Variable.t) ((map, _) : Lattice.t) =
  Lattice.VarMap.find var map *)

let rec add_constraints (known : Lattice.t) (flam : Flambda.t) : (Lattice.t * Lattice.varInfo) =
  match flam with
  | Flambda.Var v -> (known, Lattice.getVar known v)
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body; _} ->
    let _ = print_string ("In a let with variable " ^ (Variable.unique_name var) ^ "\n") in
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
   * Note that in flambda, apply is var(var, var, ...) so we can't glean any more info
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
  | Flambda.Proved_unreachable -> (known, Lattice.NoInfo) (* TODO: return _|_ *)
  | _ -> (known, Lattice.NoInfo)
and add_constraints_named (known : Lattice.t) (named : Flambda.named) : (Lattice.t * Lattice.varInfo) =
  match named with
  (* Symbols are handles for constants from separate compilation units. We might need to check
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
            |   Allocated_const.Float _
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
     let fieldInfo = if fieldInfo = Lattice.NoInfo then Lattice.SymbolField (sym, idx) else Lattice.NoInfo in
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
          (match Lattice.getVarOpt known var with
          | Some Lattice.NoInfo -> Lattice.ScalarInfo(LB.zero, UB.PosInf) (* Should this be NoInfo? *)
          | Some (Lattice.ArrayOfLength _) ->
              Lattice.ScalarInfo (LB.zero, UB.UB (UB.LenAtom var))
          | Some (Lattice.SymbolField (x, i)) ->
              Lattice.ScalarInfo(LB.zero, UB.UB (UB.LenSymAtom (x, i)))
            (* HACK TODO (None case): We should be assuming NoInfo here, and only using these if the variable is not free *)
          | None -> Lattice.ScalarInfo(LB.zero, UB.UB (UB.LenAtom var))
          | Some _ -> raise TypeMismatch
          )
          (* Lattice.ScalarInfo (LB.zero, UB.UB (UB.LenAtom var)) *)
       | (Lambda.Pintcomp comparison, left :: right :: []) ->
        get_comparison_info known comparison left right
       | _ -> Lattice.NoInfo
      in (known, info)
  | Flambda.Expr expr -> add_constraints known expr
  | _ -> (known, Lattice.NoInfo)

and get_comparison_info (sigma : Lattice.t)
                        (comparison : Lambda.comparison)
                        (leftVar : Variable.t)
                        (rightVar : Variable.t) =
  let module L = Lattice in
  let exclusive x = x in (* TODO-someday: Fix me. Please. *)
  let minUB a b = match (a, b) with
    | (L.ScalarInfo (_, aa), L.ScalarInfo (_, bb)) ->
      let j = UB.join aa bb in
      if j = bb      then aa
      else if j = aa then bb
                     else aa
    | _ -> raise (Impossible "minUB") in
  let maxLB a b = match (a, b) with
    | (L.ScalarInfo (aa, _), L.ScalarInfo (bb, _)) ->
      let j = LB.join aa bb in
      if j = bb      then aa
      else if j = aa then bb
                     else aa
    | _ -> raise (Impossible "maxLB") in
  let left = Lattice.getVar sigma leftVar in
  let right = Lattice.getVar sigma rightVar in
  (* TODO-someday: implement these, but less bad. *)
  let mapFromTwo (k1, v1) (k2, v2) =
    Lattice.VarMap.add k1 v1 (Lattice.VarMap.singleton k2 v2) in
  let mkLT a b = Lattice.ScalarInfo (LB.NegInf, (minUB a (exclusive b))) in
  let mkLE a b = Lattice.ScalarInfo (LB.NegInf, minUB a b) in
  let mkGT a b = Lattice.ScalarInfo (maxLB a b, UB.PosInf) in
  let mkGE a b = Lattice.ScalarInfo (maxLB a b, UB.PosInf) in
  let mkEQ _ b = b in
  let b x = Lattice.BoolInfo x in
  match comparison with
  | Lambda.Clt -> b{L.ifTrue = mapFromTwo  (leftVar, mkLT left right) (rightVar, mkGT right left);
                    L.ifFalse = mapFromTwo (leftVar, mkGE left right) (rightVar, mkLE right left)}
  | Lambda.Cgt -> b{L.ifTrue = mapFromTwo  (leftVar, mkGT left right) (rightVar, mkLT right left);
                    L.ifFalse = mapFromTwo (leftVar, mkLE left right) (rightVar, mkGE right left)}
  | Lambda.Cle -> b{L.ifTrue = mapFromTwo  (leftVar, mkLE left right) (rightVar, mkGE right left);
                    L.ifFalse = mapFromTwo (leftVar, mkGT left right) (rightVar, mkLT right left)}
  | Lambda.Cge -> b{L.ifTrue = mapFromTwo  (leftVar, mkGE left right) (rightVar, mkLE right left);
                    L.ifFalse = mapFromTwo (leftVar, mkLT left right) (rightVar, mkGT right left)}
  | Lambda.Ceq -> b{L.ifTrue = mapFromTwo  (leftVar, mkEQ left right) (rightVar, mkEQ right left);
                    L.ifFalse = Lattice.VarMap.empty}
  | Lambda.Cneq -> Lattice.NoInfo
