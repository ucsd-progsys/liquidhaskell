module C = FixConstraint
module P = Ast.Predicate
module E = Ast.Expression
module Sy = Ast.Symbol
module Su = Ast.Subst

module Misc = FixMisc open Misc.Ops

let rec defs_of_pred (edefs, pdefs) ((p, _) as pred) = 
  match p with
    | Ast.Atom ((Ast.Var v, _), Ast.Eq, e) when not(P.is_tauto pred) -> Sy.SMap.add v e edefs, pdefs
    | Ast.And [Ast.Imp ((Ast.Bexp (Ast.Var v1, _), _), p1), _; 
	       Ast.Imp (p2, (Ast.Bexp (Ast.Var v2, _), _)), _] when v1 = v2 && p1 = p2 && not(P.is_tauto pred) -> 
	edefs, Sy.SMap.add v1 p1 pdefs
    | Ast.And preds -> List.fold_left defs_of_pred (edefs, pdefs) preds
    | _ -> edefs, pdefs

let some_def_applied = ref false
let rec expr_apply_defs edefs pdefs ((e, _) as expr) = 
  let current_some_def_applied = !some_def_applied in
    some_def_applied := false;
    let expr'' =
      match e with
	| Ast.Con _ -> expr
	| Ast.Var v -> 
	    begin
	      try
		let expr' = Sy.SMap.find v edefs in
		  some_def_applied := true;
		  expr'
	      with Not_found -> expr
	    end
	| Ast.App (v, es) -> 
	    let edefs' = Sy.SMap.remove v edefs in
	      Ast.eApp (v, List.map (expr_apply_defs edefs' pdefs) es)
	| Ast.Bin (e1, op, e2) -> 
	    Ast.eBin (expr_apply_defs edefs pdefs e1, op, expr_apply_defs edefs pdefs e2)
	| Ast.Ite (p, e1, e2) -> 
	    Ast.eIte (pred_apply_defs edefs pdefs p, 
		      expr_apply_defs edefs pdefs e1,
		      expr_apply_defs edefs pdefs e2)
	| Ast.Fld (v, e) -> 
	    let v' = 
	      try
		match Sy.SMap.find v edefs with
		  | (Ast.Var v'', _) -> 
		      some_def_applied := true;
		      v''
		  | _ -> v
	      with Not_found -> v
	    in
	      Ast.eFld (v', expr_apply_defs edefs pdefs e)
        | _ -> assertf "Simplification.expr_apply_defs TODO" 
    in
      if !some_def_applied then
	let expr''' = expr_apply_defs edefs pdefs expr'' in
	  some_def_applied := current_some_def_applied;
	  expr'''
      else
	begin
	  some_def_applied := current_some_def_applied;
	  expr''
	end

and pred_apply_defs edefs pdefs ((p, _) as pred) =
  let current_some_def_applied = !some_def_applied in
    some_def_applied := false;
    let pred'' =
      match p with
	| Ast.And ps -> List.map (pred_apply_defs edefs pdefs) ps |> Ast.pAnd
	| Ast.Or ps -> List.map (pred_apply_defs edefs pdefs) ps |> Ast.pOr
	| Ast.Not p -> pred_apply_defs edefs pdefs p |> Ast.pNot
	| Ast.Imp (p, q) -> Ast.pImp (pred_apply_defs edefs pdefs p, pred_apply_defs edefs pdefs q)
	| Ast.Bexp (Ast.Var v, _) ->
	    begin
	      try
		let expr' = Sy.SMap.find v edefs in
		  some_def_applied := true;
		  Ast.pBexp expr'
	      with Not_found ->
		try
		  let pred' = Sy.SMap.find v pdefs in
		    some_def_applied := true;
		    pred'
		with Not_found ->
		  pred
	    end
	| Ast.Atom (e1, brel, e2) ->
	    Ast.pAtom (expr_apply_defs edefs pdefs e1, brel, expr_apply_defs edefs pdefs e2)
	| Ast.Forall (qs, p) ->
	    let vs = List.map fst qs in
	    let edefs' = List.fold_left (fun defs v -> Sy.SMap.remove v defs) edefs vs in
	    let pdefs' = List.fold_left (fun defs v -> Sy.SMap.remove v defs) pdefs vs in
	      Ast.pForall (qs, pred_apply_defs edefs' pdefs' p)
	| _ -> pred
    in
      if !some_def_applied then
	let pred''' = pred_apply_defs edefs pdefs pred'' in
	  some_def_applied := current_some_def_applied;
	  pred'''
      else 
	begin
	  some_def_applied := current_some_def_applied;
	  pred''
	end

let subs_apply_defs edefs pdefs subs =
  List.map (fun (s, e) -> s, expr_apply_defs edefs pdefs e) subs

let kvar_apply_defs edefs pdefs (subs, sym) = 
  subs_apply_defs edefs pdefs subs, sym

let simplify_subs subs =
  List.filter (fun (s, e) -> not(P.is_tauto (Ast.pAtom (Ast.eVar s, Ast.Eq, e)))) subs

let simplify_kvar (subs, sym) =
  simplify_subs subs, sym

let simplify_t t = 
  let env_ps, pfree_env = (* separate concrete predicates from refinement templates *)
    Sy.SMap.fold 
      (fun bv reft (ps, env) -> 
	 let vv = C.vv_of_reft reft in
	 let bv_expr = Ast.eVar bv in
	 let sort = C.sort_of_reft reft in
	 let reft_ps, reft_ks = C.preds_kvars_of_reft reft in
	   (List.rev_append (List.map (fun p -> P.subst p vv bv_expr) reft_ps) ps,
	    if reft_ks = [] then env else Sy.SMap.add bv (vv, sort, reft_ks) env)
      ) (C.env_of_t t) ([], Sy.SMap.empty) in
  let lhs = C.lhs_of_t t in
  let lhs_vv = C.vv_of_reft lhs in
  let lhs_ps, lhs_ks = C.preds_kvars_of_reft lhs in
  let body_pred = Ast.pAnd (C.grd_of_t t :: List.rev_append lhs_ps env_ps) in
  let edefs, pdefs = defs_of_pred (Sy.SMap.empty, Sy.SMap.empty) body_pred in
    (*
    Printf.printf "\nbody_pred edefs map for %d\n" (C.id_of_t t);
    Sy.SMap.iter (fun v exp ->
		    Printf.printf "%s -> %s\n" (Sy.to_string v) (E.to_string exp)
		 ) edefs;
    Printf.printf "edef for lhs_vv %s = %s (simplified %s)\n" (Sy.to_string lhs_vv) 
      (try Sy.SMap.find lhs_vv edefs |> E.to_string with Not_found -> "none")
      (try 
	 Sy.SMap.find lhs_vv edefs 
         |> expr_apply_defs edefs pdefs 
	 |> E.to_string with Not_found -> "none");
    *)
  let kvar_to_simple_Kvar (subs, sym) = C.Kvar (subs |> Su.to_list |> subs_apply_defs edefs pdefs |> simplify_subs |> Su.of_list, sym) in
  let senv = 
    Sy.SMap.mapi (fun bv (vv, sort, ks) -> 
		    List.map kvar_to_simple_Kvar ks |>	C.make_reft vv sort) pfree_env in
(*     Printf.printf "body_pred: %s\n" (P.to_string body_pred); *)
  let sgrd' = pred_apply_defs edefs pdefs body_pred |> Ast.simplify_pred in
  let sgrd = 
    try
      Ast.pAnd [sgrd'; Ast.pAtom (Ast.eVar lhs_vv, Ast.Eq, Sy.SMap.find lhs_vv edefs |> expr_apply_defs edefs pdefs)]
    with Not_found -> sgrd' in
(*    Printf.printf "simplified body_pred: %s\n" (P.to_string sgrd); *)
  let slhs = List.map kvar_to_simple_Kvar lhs_ks |> C.make_reft (C.vv_of_reft lhs) (C.sort_of_reft lhs) in
  let rhs = C.rhs_of_t t in
  let rhs_ps, rhs_ks = C.preds_kvars_of_reft rhs in
  let srhs_pred = pred_apply_defs edefs pdefs (Ast.pAnd rhs_ps) |> Ast.simplify_pred in
  let srhs_ks = List.map kvar_to_simple_Kvar rhs_ks in
  let srhs =  (if P.is_tauto srhs_pred then srhs_ks else (C.Conc srhs_pred) :: srhs_ks) |> 
      C.make_reft (C.vv_of_reft rhs) (C.sort_of_reft rhs) in
    C.make_t senv sgrd slhs srhs (Some (C.id_of_t t)) (C.tag_of_t t)

let simplify_ts ts =
  (* drop t if its rhs is a k variable that is not read *)
  let ts_sofar = ref ts in
  let pruned = ref true in
    while !pruned && !ts_sofar <> [] do
      let pruned_ts, rest_ts = 
	List.partition
	  (fun t ->
	     match C.rhs_of_t t |> C.preds_kvars_of_reft with
	       | [], [(_, sy)] ->
		   List.for_all 
		     (fun t' -> 
			List.for_all (fun (_, sy') -> sy <> sy') 
			  (Sy.SMap.fold 
			     (fun _ reft sofar -> List.rev_append (C.kvars_of_reft reft) sofar) 
			     (C.env_of_t t') (C.lhs_of_t t' |> C.kvars_of_reft))
		     ) !ts_sofar
	       | _ -> false
	  ) !ts_sofar in
	ts_sofar := rest_ts;
	pruned := pruned_ts <> []
    done;
    !ts_sofar

let is_tauto_t t =
  match C.rhs_of_t t |> C.ras_of_reft with
    | [] -> true
    | [C.Conc p] -> P.is_tauto p 
    | _ -> false

  
