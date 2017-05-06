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
(*
let unwrap (x : 'a option) : 'a =
  match x with
  | Some y -> y
  | None -> raise (Failure "unwrap failed")*)

(* Idea for proved-unreachable:
   Raise UnreachableBot containing the abstractions of some
   of the arguments to signal an unreachable path.
   At join points in the AST, use a try-with to detect unreachable statements.
   This would require a persistent whole-AST lattice which isn't hard but
   we don't have the time in this project.
   This idea could also be used in Array_lattice.Lattice.applyBoolInfo
   if we split it up into two functions (otherwise, which one is throwing)
   the exception??
  exception UnreachableBot of Static_exception.t * (L.varInfo list)
 *)


(* For how we should have done the lattices:
  we should have a fancy context type that is immutable...
  Don't know enough about the requirements.
  Gotta handle free variables and symbols well.
  Maybe encapsulate the varinfo? probably not.
  *)

let rec add_constraints (al : LL.t) (sigma : L.t) (flam : Flambda.t) : (L.t * L.varInfo) =
  let add_c sigma flam = add_constraints al sigma flam in
  let add_c_named sigma flam = add_constraints_named al sigma flam in
  let updateOut s = LL.updateOut al flam in
  (match flam with
  | Flambda.Var v -> (sigma, Lattice.getVar_top sigma v)
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body; _} ->
    let _ = print_string ("In a let with variable " ^ (Variable.unique_name var) ^ "\n") in
    let (in_lattice, deInfo) = addc_named sigma defining_expr in
    let sigma = updateOut (Lattice.updateVar var deInfo sigma) in
    add_c sigma body
  (* Right now, we ignore mutable variables. no memory woohoo *)
  | Flambda.Let_mutable {Flambda.body; _} -> add_c sigma body
  | Flambda.Let_rec (defs, body) ->
    let add_def sigma (name, def) =
      let (sigma, defInfo) = add_c_named sigma def
      in updateOut (Lattice.updateVar name defInfo sigma) in
    let sigma = List.fold_left add_def sigma defs in
    add_constraints sigma body
  (* We don't know anything about functions right now, although maybe we ought to.
   * Note that in flambda, apply is var(var, var, ...) so we can't glean any more info
   * by traversing. *)
  | Flambda.Apply _ -> (sigma, Lattice.Anything)
  (* Object oriented stuff, ew *)
  | Flambda.Send _ -> (sigma, Lattice.Anything)
  (* Assignment of a mutable variable. We might want to return to this later *)
  | Flambda.Assign _ -> (sigma, Lattice.Anything)
  | Flambda.If_then_else (_, trueBranch, falseBranch) ->
    let (sigmaTrue, trueInfo) = add_c sigma trueBranch in
    let (sigmaFalse, falseInfo) = add_c sigma falseBranch in
    let sigmaNew = updateOut (Lattice.join sigmaTrue sigmaFalse) in
    (sigmaNew, Lattice.joinVarInfo trueInfo falseInfo)
  | Flambda.Switch (_, {Flambda.consts; Flambda.blocks; Flambda.failaction}) ->
    let add_case (sigma, possibleInfos) (_, case) =
      let (sigma2, caseInfo) = add_constraints sigma case
      in (Lattice.join sigma sigma2, caseInfo :: possibleInfos)
    in
    let (sigma, possibleInfos) = List.fold_left add_case (L.bot, []) consts in
    let (sigma, possibleInfos) = List.fold_left add_case (sigma, possibleInfos) blocks in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Lattice.Anything in
    begin match failaction with
     | None -> (updateOut sigma, switchInfo)
     | Some action -> let (sigma, actionInfo) = add_c sigma action in
                      (updateOut sigma, L.joinVarInfo switchInfo actionInfo)
    end
  | Flambda.String_switch (_, cases, fallthrough) ->
    let add_case (sigma, possibleInfos) (_, case) =
      let (sigma2, caseInfo) = add_constraints sigma case
      in (Lattice.join sigma sigma2, caseInfo :: possibleInfos) in
    let (sigma, possibleInfos) = List.fold_left add_case (L.bot, []) cases in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Lattice.Anything in
    begin match fallthrough with
     | None -> (updateOut sigma, switchInfo)
     | Some action -> let (sigma, actionInfo) = add_constraints sigma action in
                      (updateOut sigma, L.joinVarInfo switchInfo actionInfo)
    end
  | Flambda.Try_with (exp, _, handler) -> (* Jacob: what even is the middle variable?? what does it represent?? *)
    let (sigma, expInfo) = add_c sigma exp in
    let (sigma, handlerInfo) = add_c sigma handler in
    (sigma, Lattice.joinVarInfo expInfo handlerInfo)
  | Flambda.While (cond, body) ->
    let (sigma, _) = add_c sigma cond in
    let (sigma, _) = add_c sigma body in
    (* In general, we can't know anything about a while loop because who knows if the
     * condition will ever be true *)
    (sigma, Lattice.Anything)
  | Flambda.For { Flambda.body; _; } -> add_c sigma body (* TODO: Fix this!!! *)
  | Flambda.Proved_unreachable -> (Lattice.bot, Lattice.Anything) (* TODO: return _|_ *)
  | _ -> (sigma, Lattice.Anything)
  )
and add_constraints_named (al : LL.t)
                          (sigma : Lattice.t)
                          (named : Flambda.named)
                          : (Lattice.t * Lattice.varInfo) =
  (* It's really dumb that this could modify the whole program lattice.
     Flambda is *supposed* to be ANF-form but it's not really. *)
  match named with
  (* Symbols are handles for constants from separate compilation units. We might need to check
   * for arraylength or something here. *)
  | Flambda.Symbol sym -> (sigma, L.getSymField_top sigma (sym, 0)) (* Jacob: Sinan, pls review for sanity *)
  | Flambda.Const c -> (sigma, (match c with
                                | Flambda.Int i -> L.ScalarInfo (SC.of_int i)
                                | _ -> L.Anything))
  | Flambda.Allocated_const c ->
    (sigma, match c with
            | Allocated_const.Int32 i -> L.ScalarInfo (SC.of_int32 i)
            | Allocated_const.Int64 i -> L.ScalarInfo (SC.of_int64 i)
            | Allocated_const.Nativeint ni -> L.ScalarInfo (SC.of_nativeint ni)
            |   Allocated_const.Float _
              | Allocated_const.String _
              | Allocated_const.Float_array _
              | Allocated_const.Immutable_string _
              | Allocated_const.Immutable_float_array _ -> Lattice.Anything
    )
  (* Once again, mutables might be useful to look at later. *)
  | Flambda.Read_mutable _ -> (sigma, Lattice.Anything)
  | Flambda.Read_symbol_field (sym, idx) ->
     (sigma, Lattice.getSymField_top sigma (sym, idx))
  | Flambda.Set_of_closures {Flambda.function_decls = {Flambda.funs; _}; _} ->
     (sigma, Lattice.Anything) (* TODO: fix this up? *)
     (* let bindings = Variable.Map.bindings funs in
     let addBindings sigma (_, ({Flambda.body;} : Flambda.function_declaration)) =
       let (sigma2, _) = add_constraints sigma body in sigma2 in
     (List.fold_left addBindings sigma bindings, Lattice.NoInfo) *)
  | Flambda.Prim (prim, vars, _) ->
      (sigma, match (prim, vars) with
       (* Ensure we're only looking at the length of a single array. *)
       | (Lambda.Parraylength _, [var]) ->
          (match Lattice.getVar_top sigma var with
          | Lattice.ArrayOfLength sc -> Lattice.ScalarInfo sc
          | Lattice.ScalarInfo sc -> Lattice.ScalarInfo sc (* It's not a very type-safe lattice... *)
          | Lattice.Anything -> Lattice.ScalarInfo SC.nonnegative
          | Lattice.BoolInfo _ -> raise TypeMismatch (* Nevertheless, this should never happen *)
          )
       | (Lambda.Pintcomp comparison, [left, right]) ->
            get_comparison_info sigma comparison left right
       | _ -> Lattice.Anything
      )
  | Flambda.Expr expr -> add_constraints al sigma expr
  | _ -> (sigma, Lattice.NoInfo)
and get_comparison_info (sigma : Lattice.t)
                        (comparison : Lambda.comparison)
                        (leftVar : Variable.t)
                        (rightVar : Variable.t) =
  let minUB a b = match (a, b) with
    | (L.ScalarInfo aa, L.ScalarInfo bb) ->
      let minUpper = UB.join aa.ub bb.ub in
      SC.of_upper_bound minUpper
    | _ -> raise (Impossible "minUB") in
  let maxLB a b = match (a, b) with
    | (L.ScalarInfo aa, L.ScalarInfo bb) ->
      let maxLower = LB.join aa.lb bb.lb in
      SC.of_lower_bound maxLower
    | _ -> raise (Impossible "maxLB") in
  let exclusiveUB b = SC.plus_constant 1 b
  let exclusiveLB b = SC.plus_constant -1 b
  let mapFromTwo (v1, v2) =
    Lattice.VarMap.add leftVar v1 (Lattice.VarMap.singleton rightVar v2) in
  (* TODO-someday: handle eq/neq better? *)
  let mkLT a b = Lattice.ScalarInfo (minUB a (exclusiveUB b)) in
  let mkLE a b = Lattice.ScalarInfo (minUB a b) in
  let mkGT a b = Lattice.ScalarInfo (maxLB a (exclusiveLB b)) in
  let mkGE a b = Lattice.ScalarInfo (maxLB a b) in
  let mkEQ _ b = b in
  let left = Lattice.getVar sigma leftVar in
  let right = Lattice.getVar sigma rightVar in
  let b x = Lattice.BoolInfo x in
  match comparison with
  | Lambda.Clt -> b{L.ifTrue = mapFromTwo  (mkLT left right, mkGT right left);
                    L.ifFalse = mapFromTwo (mkGE left right, mkLE right left)}
  | Lambda.Cgt -> b{L.ifTrue = mapFromTwo  (mkGT left right, mkLT right left);
                    L.ifFalse = mapFromTwo (mkLE left right, mkGE right left)}
  | Lambda.Cle -> b{L.ifTrue = mapFromTwo  (mkLE left right, mkGE right left);
                    L.ifFalse = mapFromTwo (mkGT left right, mkLT right left)}
  | Lambda.Cge -> b{L.ifTrue = mapFromTwo  (mkGE left right, mkLE right left);
                    L.ifFalse = mapFromTwo (mkLT left right, mkGT right left)}
  | Lambda.Ceq -> b{L.ifTrue = mapFromTwo  (mkEQ left right, mkEQ right left);
                    L.ifFalse = Lattice.bot}
  | Lambda.Cneq -> b{L.ifTrue = Lattice.bot;
                     L.ifFalse = mapFromTwo (mkEQ left right, mkEQ right left)}
