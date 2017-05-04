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
