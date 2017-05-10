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
   This idea could also be used in Array_lattice.Lattice.appBoolInfo
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

type arith_kind = ADD | SUB

let rec add_constraints (flam : Flambda.t) (sigma : L.t) : (L.t * L.varInfo) =
  let add_c (sigma : Lattice.t) (flam : Flambda.t) : (L.t * L.varInfo)  = add_constraints flam sigma in
  let add_c_named name sigma flam : (L.t * L.varInfo) = add_constraints_named name flam sigma in
  (match flam with
  | Flambda.Var v -> (sigma, Lattice.getVar_top v sigma)
  | Flambda.Let {Flambda.var; Flambda.defining_expr; Flambda.body; _} ->
    let _ = print_string ("In a let with variable " ^ (Variable.unique_name var) ^ "\n") in
    let (in_lattice, deInfo) = add_c_named var sigma defining_expr in
    let out_lattice = Lattice.updateVar var deInfo in_lattice in
    add_c out_lattice body
  (* Right now, we ignore mutable variables. no memory woohoo *)
  | Flambda.Let_mutable {Flambda.body; _} -> add_c sigma body
  | Flambda.Let_rec (defs, body) ->
    let add_def sigma (name, def) =
      let (sigma, defInfo) = add_c_named name sigma def
      in (Lattice.updateVar name defInfo sigma)
    in
    let sigma = List.fold_left add_def sigma defs in
    add_c sigma body
  (* We don't know anything about functions right now, although maybe we ought to.
   * Note that in flambda, apply is var(var, var, ...) so we can't glean any more info
   * by traversing. *)
  | Flambda.Apply _ -> (sigma, Anything)
  (* Object oriented stuff, ew *)
  | Flambda.Send _ -> (sigma, Anything)
  (* Assignment of a mutable variable. We might want to return to this later *)
  | Flambda.Assign _ -> (sigma, Anything)
  | Flambda.If_then_else (v, trueBranch, falseBranch) ->
    let sigmaIn = Lattice.computeBoolInfo (Key.of_var v) sigma in
    let (sigmaTrue, trueInfo) = add_c sigmaIn.ifTrue trueBranch in
    let (sigmaFalse, falseInfo) = add_c sigmaIn.ifFalse falseBranch in
    let sigmaNew = (Lattice.join sigmaTrue sigmaFalse) in
    (sigmaNew, Lattice.joinVarInfo trueInfo falseInfo)
  | Flambda.Switch (_, {Flambda.consts; Flambda.blocks; Flambda.failaction}) ->
    let add_case (sigma, possibleInfos) (_, case) =
      let (sigma2, caseInfo) = add_c sigma case
      in (Lattice.join sigma sigma2, caseInfo :: possibleInfos)
    in
    let (sigma, possibleInfos) = List.fold_left add_case (L.bot, []) consts in
    let (sigma, possibleInfos) = List.fold_left add_case (sigma, possibleInfos) blocks in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Anything in
    begin match failaction with
     | None -> (sigma, switchInfo)
     | Some action -> let (sigma, actionInfo) = add_c sigma action in
                      (sigma, L.joinVarInfo switchInfo actionInfo)
    end
  | Flambda.String_switch (_, cases, fallthrough) ->
    let add_case (sigma, possibleInfos) (_, case) =
      let (sigma2, caseInfo) = add_c sigma case
      in (Lattice.join sigma sigma2, caseInfo :: possibleInfos) in
    let (sigma, possibleInfos) = List.fold_left add_case (L.bot, []) cases in
    let switchInfo = match possibleInfos with
                      | x::xs -> List.fold_right Lattice.joinVarInfo xs x
                      | [] -> Anything in
    begin match fallthrough with
     | None -> (sigma, switchInfo)
     | Some action -> let (sigma, actionInfo) = add_c sigma action in
                      (sigma, L.joinVarInfo switchInfo actionInfo)
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
    (sigma, Anything)
  | Flambda.For for_loop ->
     let fromVal = for_loop.Flambda.from_value in
     let toVal = for_loop.Flambda.to_value in
     let bv = for_loop.Flambda.bound_var in
     let bvConstraint = ScalarInfo {lb = LB.of_var fromVal; ub = UB.of_var toVal} in
     let sigma = Lattice.updateVar bv bvConstraint sigma in
     add_c sigma for_loop.Flambda.body
  | Flambda.Proved_unreachable -> (Lattice.bot, Anything)
  | _ -> (sigma, Anything)
  )
and add_constraints_named (letBound : Variable.t)
                          (named : Flambda.named)
                          (sigma : Lattice.t)
                          : (Lattice.t * Lattice.varInfo) =
  (* It's really dumb that this could modify the whole program lattice.
     Flambda is *supposed* to be ANF-form but it's not really. *)
  match named with
  (* Symbols are handles for constants from separate compilation units. We might need to check
   * for arraylength or something here. *)
  | Flambda.Symbol sym -> (sigma, L.getSymField_top (sym, 0) sigma) (* Jacob: Sinan, pls review for sanity *)
  | Flambda.Const c -> (sigma, (match c with
                                | Flambda.Int i -> ScalarInfo (SC.of_int i)
                                | _ -> Anything))
  | Flambda.Allocated_const c ->
    (sigma, match c with
            | Allocated_const.Int32 i -> ScalarInfo (SC.of_int32 i)
            | Allocated_const.Int64 i -> ScalarInfo (SC.of_int64 i)
            | Allocated_const.Nativeint ni -> ScalarInfo (SC.of_nativeint ni)
            |   Allocated_const.Float _
              | Allocated_const.String _
              | Allocated_const.Float_array _
              | Allocated_const.Immutable_string _
              | Allocated_const.Immutable_float_array _ -> Anything
    )
  (* Once again, mutables might be useful to look at later. *)
  | Flambda.Read_mutable _ -> (sigma, Anything)
  | Flambda.Read_symbol_field (sym, idx) ->
     (sigma, Lattice.getSymField_top (sym, idx) sigma)
  | Flambda.Set_of_closures _ ->
     (sigma, Anything) (* TODO: fix this up? *)
  (*| Flambda.Set_of_closures {Flambda.function_decls = {Flambda.funs; _}; _} ->
      let bindings = Variable.Map.bindings funs in
     let addBindings sigma (_, ({Flambda.body;} : Flambda.function_declaration)) =
       let (sigma2, _) = add_constraints sigma body in
       sigma2
     in
     (List.fold_left addBindings sigma bindings, Anything) *)
  | Flambda.Prim (prim, vars, _) ->
      (sigma, match (prim, vars) with
       (* Ensure we're only looking at the length of a single array. *)
       | (Lambda.Parraylength _, [var]) ->
          (match Lattice.getVar_top var sigma with
          | ScalarInfo sc -> ScalarInfo sc (* It's not a very type-safe lattice... *)
          | Anything -> ScalarInfo SC.nonnegative
          | BoolInfo _ -> raise TypeMismatch (* Nevertheless, this should never happen *)
          )
       | (Lambda.Pintcomp comparison, [left; right]) ->
            get_comparison_info sigma comparison left right
       | (Lambda.Paddint, [left; right]) -> Lattice.add_vars sigma left right
       | (Lambda.Psubint, [left; right]) -> Lattice.sub_vars sigma left right
       | (Lambda.Pccall desc, _) ->
          (match (desc.Primitive.prim_name, vars) with
           | ("caml_make_vect", [len; _]) ->
              let _ = print_string ("Primitive:\n" ^ desc.Primitive.prim_name) in
              ScalarInfo (SC.of_var len)
           | _ -> ScalarInfo (SC.of_var letBound))
       | _ -> Anything
      )
  | Flambda.Expr expr -> add_constraints expr sigma
  | _ -> (sigma, Anything)
and get_comparison_info (sigma : Lattice.t)
                        (comparison : Lambda.comparison)
                        (leftVar : Variable.t)
                        (rightVar : Variable.t) =
  (* TODO: check for Anything *)
  print_string "Checking comparison info\n";
  Lattice.print Format.std_formatter sigma;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  print_string (Variable.unique_name leftVar);
  print_newline ();
  print_string (Variable.unique_name rightVar);
  print_newline ();
  let minUB a b = SC.of_upper_bound (UB.meet a.ub b.ub) in
  let maxLB a b = SC.of_lower_bound (LB.meet a.lb b.lb) in
  let exclusiveUB b = SC.plus_constant Int64.minus_one b in
  let exclusiveLB b = SC.plus_constant Int64.one b in
  let mapFromTwo (v1, v2) =
    Key.Map.add (Key.of_var leftVar) v1
               (Lattice.singleton (Key.of_var rightVar) v2) in
  (* TODO-someday: handle eq/neq better? *)
  let mkLT a b = ScalarInfo (minUB a (exclusiveUB b)) in
  let mkLE a b = ScalarInfo (minUB a b) in
  let mkGT a b = ScalarInfo (maxLB a (exclusiveLB b)) in
  let mkGE a b = ScalarInfo (maxLB a b) in
  let mkEQ _ b = ScalarInfo b in
  let left = match Lattice.getVar_top leftVar sigma with
             | ScalarInfo x -> x
             | _ -> raise (Impossible "get_comparison_info:left") in
  let right = match Lattice.getVar_top rightVar sigma with
             | ScalarInfo x -> x
             | _ -> raise (Impossible "get_comparison_info:right") in
  print_string "Left:\n";
  SC.print Format.std_formatter left;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  print_string "Right:\n";
  SC.print Format.std_formatter right;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  print_string "\n";
  let eub = exclusiveUB right in
  let ltInfo = minUB left (exclusiveUB right) in
  let meetInfo = SC.meet ltInfo left in
  SC.print Format.std_formatter eub;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  SC.print Format.std_formatter ltInfo;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  SC.print Format.std_formatter meetInfo;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  let ltMap = mapFromTwo (mkLT left right, mkGT right left) in
  Lattice.print Format.std_formatter ltMap;
  Format.pp_print_flush Format.std_formatter ();
  print_newline ();
  let b x = BoolInfo x in
  match comparison with
  | Lambda.Clt -> b{ifTrue = mapFromTwo  (mkLT left right, mkGT right left);
                    ifFalse = mapFromTwo (mkGE left right, mkLE right left)}
  | Lambda.Cgt -> b{ifTrue = mapFromTwo  (mkGT left right, mkLT right left);
                    ifFalse = mapFromTwo (mkLE left right, mkGE right left)}
  | Lambda.Cle -> b{ifTrue = mapFromTwo  (mkLE left right, mkGE right left);
                    ifFalse = mapFromTwo (mkGT left right, mkLT right left)}
  | Lambda.Cge -> b{ifTrue = mapFromTwo  (mkGE left right, mkLE right left);
                    ifFalse = mapFromTwo (mkLT left right, mkGT right left)}
  | Lambda.Ceq -> b{ifTrue = mapFromTwo  (mkEQ left right, mkEQ right left);
                    ifFalse = Lattice.bot}
  | Lambda.Cneq -> b{ifTrue = Lattice.bot;
                     ifFalse = mapFromTwo (mkEQ left right, mkEQ right left)}



