(* translation to Q'ARMC *)


module C  = FixConstraint
module Co = Constants 
module Sy = Ast.Symbol
module Su = Ast.Subst
module P = Ast.Predicate
module E = Ast.Expression
module StrMap = Map.Make (struct type t = string let compare = compare end)
module StrSet = Set.Make (struct type t = string let compare = compare end)
module Misc = FixMisc open Misc.Ops

let strlist_to_strset = List.fold_left (fun s x -> StrSet.add x s) StrSet.empty

(* Andrey: TODO move to ast.ml? *)
let pred_is_atomic (p, _) =
  match p with
    | Ast.True | Ast.False | Ast.Bexp _ | Ast.Atom _ -> true
    | Ast.And _ | Ast.Or _ | Ast.Not _ | Ast.Imp _ | Ast.Forall _ -> false

let pred_is_true (p, _) = 
  match p with 
    | Ast.True -> true
    | Ast.Atom (e1, Ast.Eq, e2) -> E.to_string e1 = E.to_string e2 
    | _ -> false

let neg_brel = function 
  | Ast.Eq -> Ast.Ne
  | Ast.Ne -> Ast.Eq
  | Ast.Gt -> Ast.Le
  | Ast.Ge -> Ast.Lt
  | Ast.Lt -> Ast.Ge
  | Ast.Le -> Ast.Gt

let rec push_neg ?(neg=false) ((p, _) as pred) =
  match p with
    | Ast.True -> if neg then Ast.pFalse else pred
    | Ast.False -> if neg then Ast.pTrue else pred
    | Ast.Bexp _ -> if neg then Ast.pNot pred else pred
    | Ast.Not p -> push_neg ~neg:(not neg) p
    | Ast.Imp (p, q) -> 
	if neg then Ast.pAnd [push_neg p; push_neg ~neg:true q]
	else Ast.pImp (push_neg p, push_neg q)
    | Ast.Forall (qs, p) -> 
	let pred' = Ast.pForall (qs, push_neg ~neg:false p) in
	  if neg then Ast.pNot pred' else pred'
    | Ast.And ps -> List.map (push_neg ~neg:neg) ps |> if neg then Ast.pOr else Ast.pAnd
    | Ast.Or ps -> List.map (push_neg ~neg:neg) ps |> if neg then Ast.pAnd else Ast.pOr
    | Ast.Atom (e1, brel, e2) -> if neg then Ast.pAtom (e1, neg_brel brel, e2) else pred

(* Andrey: TODO flatten nested conjunctions/disjunctions *)
let rec simplify_tauto ((p, _) as pred) =
  match p with
    | Ast.Not p -> Ast.pNot (simplify_tauto p)
    | Ast.Imp (p, q) -> Ast.pImp (simplify_tauto p, simplify_tauto q) 
    | Ast.Forall (qs, p) -> Ast.pForall (qs, simplify_tauto p)
    | Ast.And ps -> 
	let ps' = List.map simplify_tauto ps |> List.filter (fun p -> not(P.is_tauto p)) in
	  if List.mem Ast.pFalse ps' then Ast.pFalse else
	    begin
	      match ps' with
		| [] -> Ast.pTrue
		| [p'] -> p'
		| _ :: _ -> Ast.pAnd ps'
	    end
    | Ast.Or ps -> 
	let ps' = List.map simplify_tauto ps in
	  if List.exists P.is_tauto ps' then Ast.pTrue else 
	    begin
	      match ps' with
		| [] -> Ast.pFalse
		| [p'] -> p'
		| _ :: _ -> Ast.pOr ps'
	    end
    | _ -> pred

let rec partition_pred_defs edefs pdefs ((p, _) as pred) = 
  match p with
    | Ast.Atom ((Ast.Var v, _), Ast.Eq, e) -> Ast.pTrue, Sy.SMap.add v e edefs, pdefs
    | Ast.And [Ast.Imp ((Ast.Bexp (Ast.Var v1, _), _), p1), _; 
	       Ast.Imp (p2, (Ast.Bexp (Ast.Var v2, _), _)), _] when v1 = v2 && p1 = p2 -> 
	Ast.pTrue, edefs, Sy.SMap.add v1 p1 pdefs
    | Ast.And preds -> 
	let preds', edefs', pdefs' = List.fold_left 
	  (fun (preds_sofar, edefs_sofar, pdefs_sofar) p ->
	     let p'', edefs'', pdefs'' = partition_pred_defs edefs_sofar pdefs_sofar p in
	       p'' :: preds_sofar, edefs'', pdefs''
	  ) ([], edefs, pdefs) preds in
	  (Ast.pAnd preds'), edefs', pdefs'
    | _ -> pred, edefs, pdefs

let rec defs_of_pred edefs pdefs (p, _) = 
  match p with
    | Ast.Atom ((Ast.Var v, _), Ast.Eq, e) -> Sy.SMap.add v e edefs, pdefs
    | Ast.And [Ast.Imp ((Ast.Bexp (Ast.Var v1, _), _), p1), _; 
	       Ast.Imp (p2, (Ast.Bexp (Ast.Var v2, _), _)), _] when v1 = v2 && p1 = p2 -> 
	edefs, Sy.SMap.add v1 p1 pdefs
    | Ast.And preds -> 
	let edefs', pdefs' = List.fold_left 
	  (fun (edefs_sofar, pdefs_sofar) p ->
	     let edefs'', pdefs'' = defs_of_pred edefs_sofar pdefs_sofar p in
	       edefs'', pdefs''
	  ) (edefs, pdefs) preds in
	  edefs', pdefs'
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
	      Printf.printf "Applying on Bexp: %s\n" (P.to_string pred);
	      (* Andrey: TODO also consider edefs *)
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
      

let support_of_env sol env =
  Sy.SMap.fold
    (fun ksym reft sup -> 
       let vv = C.vv_of_reft reft in
       let kv = Ast.eVar ksym in
       let syms = C.preds_of_reft sol reft |>
	   List.map (fun p -> P.subst p vv kv) |> List.filter (fun p -> not(pred_is_true p)) |>
	       List.map P.support |> List.flatten
       in
	 List.fold_left (fun sup' sym -> Sy.SSet.add sym sup') sup syms
    ) env Sy.SSet.empty



let armc_true = "true"
let armc_false = "false"
let loop_pc = "loop"
let start_pc = "start"
let error_pc = "error"
let val_vname = "VVVV"
let exists_kv = "EX"
let primed_suffix = "p"
let str__cil_tmp = "__cil_tmp"

type kv_scope = {
  kvs : string list;
  kv_scope : string list StrMap.t
}

type horn_clause = {
  body_pred : Ast.pred;
  body_kvars : (Su.t * Sy.t) list;
  head_pred : Ast.pred;
  head_kvars : (Su.t * Sy.t) list;
  tag : string;
}

let sanitize_symbol s = 
  Str.global_replace (Str.regexp "@") "_at_"  s |> Str.global_replace (Str.regexp "#") "_hash_" |>
      Str.global_replace (Str.regexp "\\.") "_dot_" |> Str.global_replace (Str.regexp "'") "_q_" 

let symbol_to_armc s = Sy.to_string s |> sanitize_symbol

let var_to_armc s = Sy.to_string s |> sanitize_symbol |> String.capitalize

let subs_to_map subs = 
  List.fold_left 
    (fun m (s, e) -> 
      StrMap.add (symbol_to_armc s) e m
    ) StrMap.empty (Su.to_list subs)

let mk_data_var ?(suffix = "") kv v = 
  Printf.sprintf "_%s_%s%s%s" 
    (sanitize_symbol v) (sanitize_symbol kv) (if suffix = "" then "" else "_") suffix

	
(*
let defs_of_env state env = 
  Sy.SMap.fold 
    (fun ksym reft defs ->
       let vv = C.vv_of_reft reft in
       let kv = Ast.eVar ksym in
       let defs' = C.preds_of_reft state.sol reft |>
	   List.map (fun p -> P.subst p vv kv) |> List.filter (fun p -> not(pred_is_true p)) |>
	       List.map (defs_of_pred state) |> List.flatten
       in
	 defs' ++ defs
    ) env []
*)

let constant_to_armc = Ast.Constant.to_string
let bop_to_armc = function 
  | Ast.Plus  -> "+"
  | Ast.Minus -> "-"
  | Ast.Times -> "*"
  | Ast.Div   -> "/"
let brel_to_armc = function 
  | Ast.Eq -> "="
  | Ast.Ne -> "=\\="
  | Ast.Gt -> ">"
  | Ast.Ge -> ">="
  | Ast.Lt -> "<"
  | Ast.Le -> "=<"
let bind_to_armc (s, t) = (* Andrey: TODO support binders *)
  Printf.sprintf "%s:%s" (symbol_to_armc s) (Ast.Sort.to_string t |> sanitize_symbol)
let rec expr_to_armc (e, _) = 
  match e with
    | Ast.Con c -> constant_to_armc c
    | Ast.Var s -> var_to_armc s
    | Ast.App (s, es) -> 
	if !Co.purify_function_application then "_" else
	  let str = symbol_to_armc s in
	    if es = [] then str else
	      Printf.sprintf "f_%s(%s)" str (List.map expr_to_armc es |> String.concat ", ")
    | Ast.Bin (e1, op, e2) ->
	Printf.sprintf "(%s %s %s)" 
	  (expr_to_armc e1) (bop_to_armc op) (expr_to_armc e2)
    | Ast.Ite (ip, te, ee) -> 
	Printf.sprintf "ite(%s, %s, %s)" 
	  (pred_to_armc ip) (expr_to_armc te) (expr_to_armc ee)
    | Ast.Fld (s, e) -> 
	Printf.sprintf "fld(%s, %s)" (expr_to_armc e) (symbol_to_armc s)
and pred_to_armc ((p, _) as pred) = 
  if pred_is_true pred then 
    armc_true
  else
    match p with
      | Ast.True -> armc_true
      | Ast.False -> armc_false
      | Ast.Bexp e -> Printf.sprintf "bexp(%s)" (expr_to_armc e)
      | Ast.Not (Ast.True, _) -> armc_false
      | Ast.Not (Ast.False, _) -> armc_true
      | Ast.Not p -> Printf.sprintf "neg(%s)" (pred_to_armc p) 
      | Ast.Imp (p1, p2) -> Printf.sprintf "imp(%s, %s)" (pred_to_armc p1) (pred_to_armc p2)
      | Ast.And [] -> armc_true
      | Ast.And [p] -> pred_to_armc p
      | Ast.And [Ast.Imp ((Ast.Bexp e1, _) as p, p1), _; 
		 Ast.Imp (p2, (Ast.Bexp e2, _)), _] when e1 = e2 && p1 = p2 -> 
	  Printf.sprintf "bexp_def(%s, %s)" (pred_to_armc p) (pred_to_armc p1)
      | Ast.And (_::_ as ps) -> 
	  Printf.sprintf "(%s)" (List.map pred_to_armc ps |> String.concat ", ")
      | Ast.Or [] -> armc_false
      | Ast.Or [p] -> pred_to_armc p
      | Ast.Or (_::_ as ps) -> Printf.sprintf "(%s)" (List.map pred_to_armc ps |> String.concat "; ")
      | Ast.Atom (e1, Ast.Eq, (Ast.Ite(ip, te, ee), _)) ->
	  let ip_str = pred_to_armc ip in
	  let e1_str = expr_to_armc e1 in
	    Printf.sprintf "((%s, %s = %s); (neg(%s), %s = %s))"
	      ip_str e1_str (expr_to_armc te) 
	      ip_str e1_str (expr_to_armc ee) 
      | Ast.Atom (e1, r, e2) ->
	  Printf.sprintf "%s %s %s" 
            (expr_to_armc e1) (brel_to_armc r) (expr_to_armc e2)
      | Ast.Forall (qs,p) -> (* Andrey: TODO support forall *) 
	  Printf.sprintf "forall([%s], %s)" 
            (List.map bind_to_armc qs |> String.concat ", ") 
	    (pred_to_armc p)


let mk_kv_scope out ts wfs =
  (*  let kvs = List.map C.kvars_of_t ts |> List.flatten |> List.map snd |> 
      List.map symbol_to_armc |> (* (fun s -> Printf.sprintf "k%s" (symbol_to_armc s)) |> *)
      Misc.sort_and_compact in
  *)
  let kv_scope_wf =
    List.fold_left
      (fun m wf ->
	match C.reft_of_wf wf |> C.ras_of_reft with
	  | [C.Kvar (subs, kvar)] when Su.is_empty subs ->
	    let v = symbol_to_armc kvar in
	    let scope = 
(*	      val_vname :: *)
		(C.env_of_wf wf 
		    |> C.bindings_of_env 
		    |> List.filter 
			(fun (_, (_, typ, _)) ->
			  Ast.Sort.t_int = typ
			)
		    |> List.map fst 
		    |> List.map symbol_to_armc 
		    |> List.filter 
			(fun s -> 
			  not(Misc.is_prefix str__cil_tmp s 
			      || Misc.is_prefix "FP_" s
			      || Misc.is_prefix "Open_" s
			      || Misc.is_prefix "None_0" s
			      || Misc.is_prefix "Some_0" s
			      || Misc.is_prefix "true_0" s
			      || Misc.is_prefix "false_0" s
			      || Misc.is_prefix "Pervasives_" s
			      || Misc.is_prefix "FIXPOINTSYMBOL_" s)) 
		    |> List.sort compare) 
	    in
	    StrMap.add v scope m
	  | _ -> m
      (* Andrey: TODO handle ill-formed wf *)
      (*		 Format.printf "%a" (C.print_wf None) wf;
			 
			 failure "ERROR: kname_scope_map: ill-formed wf"
      *)
      ) StrMap.empty wfs in
  let kv_scope_t =
    List.fold_left 
      (fun m (subs, kvar) ->
	let v = symbol_to_armc kvar in
	let scope = 
	  List.filter (fun (v, (e, _)) -> 
	    match e with
	      | Ast.Var v' -> v <> v'
	      | _ -> true
	  ) (Su.to_list subs) |> 
	      List.map fst |> List.map symbol_to_armc |> strlist_to_strset in
	let scope' = try StrMap.find v m with Not_found -> StrSet.empty in
	StrMap.add v (StrSet.union scope scope') m
      ) StrMap.empty (List.map C.kvars_of_t ts |> List.flatten) in
  let kv_scope = kv_scope_wf in
  let kv_scope_old = 
    StrMap.map (fun scope -> val_vname :: (StrSet.elements scope |> List.sort compare)) kv_scope_t in
  let kvs = StrMap.fold (fun kv _ kvs -> kv :: kvs) kv_scope [] in
  (* 
  StrMap.iter (fun kv scope ->
    Printf.fprintf out "%% %s -> %s\n" kv (String.concat ", " scope)) kv_scope;
  *)
  {kvs = kvs; kv_scope = kv_scope}

let mk_data ?(suffix = "") ?(skip_kvs = []) s = 
  Printf.sprintf "[%s]"
    (List.map 
       (fun kv ->
	  try 
	    StrMap.find kv s.kv_scope |> 
		List.map (mk_data_var ~suffix:(if List.mem kv skip_kvs then "" else suffix) kv)
	  with Not_found -> failure "ERROR: mk_data: scope not found for %s" kv
       ) s.kvs |> List.flatten |> String.concat ", ")

let mk_query ?(suffix = "") s kv = 
  Printf.sprintf "k%s(%s)" 
    kv (List.map (mk_data_var ~suffix:suffix kv) (StrMap.find kv s.kv_scope) |> String.concat ", ")

let mk_var2names state = 
  List.map
    (fun kv ->
       Printf.sprintf "var2names(p(pc(k%s), data(%s)), [%s])."
	 kv
	 (List.map (mk_data_var kv) (StrMap.find kv state.kv_scope) |> String.concat ", ")
	 (List.map 
	    (fun v -> 
	       Printf.sprintf "(%s, \'%s_%s\')" (mk_data_var kv v)  v kv
	    ) (StrMap.find kv state.kv_scope) |> String.concat ", ")
    ) state.kvs |> String.concat "\n"

let mk_skip_update state kvs = 
  if kvs = [] then armc_true else
    List.map
      (fun kv ->
	 List.map 
	   (fun v -> 
	      Printf.sprintf "%s = %s"
		(mk_data_var ~suffix:primed_suffix kv v) (mk_data_var kv v)
	   ) (StrMap.find kv state.kv_scope) |> String.concat ", "
      ) kvs |> String.concat ", "

let mk_update_str from_vs to_vs updates = 
  List.map2
    (fun v vp ->
       Printf.sprintf "%s = %s" vp (try StrMap.find v updates with Not_found -> v)
    ) from_vs to_vs |> String.concat ", "

let split_scope scope = 
  match scope with
    | value :: data -> value, data
    | _ -> failure "ERROR: split_scope: empty scope %s" (String.concat ", " scope)

let reft_to_armc ?(noquery = false) ?(suffix = "") state reft = 
  let vv = C.vv_of_reft reft |> symbol_to_armc in
  let rs = C.ras_of_reft reft in
    if rs = [] then armc_true else
      List.map
	(function
	   | C.Conc pred -> pred_to_armc pred
	   | C.Kvar (subs, sym) -> 
	     failwith "AR: toQARMC.ml reft_to_armc";
	     if true (* Sy.SMap.mem sym state.sol && Sy.SMap.find sym state.sol = [] *)then 
		 armc_true  (* skip true *)
	       else
		 let subs_map = subs_to_map subs in
		 let find_subst v default = 
		   try StrMap.find v subs_map |> expr_to_armc with Not_found -> default in
		 let kv = symbol_to_armc sym in
		 let value, data = StrMap.find kv state.kv_scope |> split_scope in
		   Printf.sprintf "%s%s = %s" 
		     (if noquery then "" else (mk_query ~suffix:suffix state kv) ^ ", ")
		     (mk_data_var ~suffix:suffix kv value) 
		     (find_subst vv (mk_data_var exists_kv vv)) 
		   :: List.map
		     (fun v -> 
			Printf.sprintf "%s = %s"
			  (mk_data_var ~suffix:suffix kv v)
			  (find_subst v (mk_data_var exists_kv v))
		     ) data |> String.concat ", "
	) rs |> String.concat ", "

let mk_rule head annot_guards annot_updates id = 
  let rec annot_conj_to_armc = function
    | (g, a) :: rest -> 
	if rest = [] then Printf.sprintf "\n   %s \t%% %s\n  ]," g a
	else Printf.sprintf "\n   %s, \t%% %s%s" g a (annot_conj_to_armc rest)
    | [] -> "],"
  in
    Printf.sprintf
      "
hc(%s, [%s  %s).
" 
      head (annot_guards @ annot_updates |> List.filter (fun (g, _) -> g <> armc_true) |> annot_conj_to_armc) id

let preds_kvars_of_reft reft =
  List.fold_left 
    (fun (ps, ks) r ->
       match r with
	 | C.Conc p -> p :: ps, ks
	 | C.Kvar (subs, kvar) -> ps, (subs, kvar) :: ks
    ) ([], []) (C.ras_of_reft reft)

let t_to_horn_clause t =
  let lhs_ps, lhs_ks = C.lhs_of_t t |> preds_kvars_of_reft in
  let body_ps, body_ks = 
    Sy.SMap.fold 
      (fun bv reft (ps, ks) -> 
	 let ps', ks' = preds_kvars_of_reft (C.theta (Su.of_list [(C.vv_of_reft reft, Ast.eVar bv)]) reft) in
	   List.rev_append ps' ps, List.rev_append ks' ks
      ) (C.env_of_t t) (C.grd_of_t t :: lhs_ps, lhs_ks) in
  let head_ps, head_ks = C.rhs_of_t t |> preds_kvars_of_reft in
    {
      body_pred = Ast.pAnd body_ps |> simplify_tauto; 
      body_kvars = body_ks; 
      head_pred = Ast.pAnd head_ps |> simplify_tauto;
      head_kvars = head_ks;
      tag = try string_of_int (C.id_of_t t) with _ -> failure "ERROR: t_to_horn_clause: anonymous constraint %s" (C.to_string t)
    }

let simplify_horn_clause hc = 
  let body_edefs, body_pdefs = defs_of_pred Sy.SMap.empty Sy.SMap.empty hc.body_pred in
  let edefs, pdefs = defs_of_pred body_edefs body_pdefs hc.head_pred in
    {
      body_pred = pred_apply_defs edefs pdefs hc.body_pred |> simplify_tauto; 
      body_kvars = hc.body_kvars; 
      head_pred = pred_apply_defs edefs pdefs hc.head_pred |> simplify_tauto;
      head_kvars = hc.head_kvars; 
      tag = hc.tag
    }

let print_horn_clause hc = 
  Printf.printf "%s: %s, %s :- %s, #%d %s\n"
    hc.tag 
    (P.to_string hc.head_pred)
    (List.map (fun (subs, kvar) -> C.refa_to_string (C.Kvar (subs, kvar))) hc.head_kvars |> String.concat ", ")
    (P.to_string hc.body_pred)
    (List.length hc.body_kvars)
    (List.map (fun (subs, kvar) -> C.refa_to_string (C.Kvar (subs, kvar))) hc.body_kvars |> String.concat ", ")

    
let t_to_armc state t = 
  t_to_horn_clause t |> simplify_horn_clause |> print_horn_clause;
  let env = C.env_of_t t in
  let grd = C.grd_of_t t in
  let lhs = C.lhs_of_t t in
  let rhs = C.rhs_of_t t in
  let rhs_s = C.reft_to_string rhs in
  let tag = try string_of_int (C.id_of_t t) with _ -> 
    failure "ERROR: t_to_armc: anonymous constraint %s" (C.to_string t) in
(*   let defs = defs_of_env state env in *)
  let annot_guards = 
    Misc.map_partial
      (fun (bv, reft) ->
	 if C.ras_of_reft reft <> [] then
	   Some (reft_to_armc state (C.theta (Su.of_list [(C.vv_of_reft reft, Ast.eVar bv)]) reft),
		 C.binding_to_string (bv, reft))
	 else
	   None
      ) (env |> C.bindings_of_env)
    ++ [(pred_to_armc grd, P.to_string grd); 
	(reft_to_armc state lhs, "|- " ^ (C.reft_to_string lhs))] in
  let ps, kvs =  
    List.fold_left (fun (ps', kvs') refa ->
		      match refa with
			| C.Conc p -> p::ps', kvs'
			| C.Kvar (subs, sym) -> ps', (subs, sym)::kvs'
		   ) ([], []) (C.ras_of_reft rhs) in
(* Andrey: obsolete code
  let env_sup = support_of_env state.sol env |> Sy.SSet.elements in
    Printf.printf "Rule %s\n" tag;
    Printf.printf "Env support #%d: %s\n" 
      (List.length env_sup) (env_sup |> List.map Sy.to_string |> String.concat ", ");
    Printf.printf "Guard support %s: %s\n" 
      (P.to_string grd) 
      (P.support grd |> List.map Sy.to_string |> String.concat ", ");
*)    
    (if ps <> [] then
       [mk_rule error_pc annot_guards [(Ast.pAnd ps |> Ast.pNot |> pred_to_armc, "<: " ^ rhs_s)] tag]
     else 
       [])
    ++
      (List.map 
	 (fun (_, sym) ->
	    mk_rule (mk_query ~suffix:primed_suffix state (symbol_to_armc sym))
	      annot_guards 
	      [(reft_to_armc ~noquery:true ~suffix:primed_suffix state rhs, "<: " ^ rhs_s)]
	      tag
	 ) kvs)


(*
  make -f Makefile.fixtop && ./f -latex /tmp/main.tex -armc /tmp/a.pl tests/pldi08-max.fq && cat /tmp/a.pl

tests:

for file in `ls pldi08-*-atom.fq`; do ../f -latex /tmp/main.tex -armc /tmp/a.pl $file; head -n 1 /tmp/a.pl; armc a.pl | grep correct; done

pldi08-arraymax-atom.fq  pass
pldi08-max-atom.fq       pass
pldi08-foldn-atom.fq     pass
pldi08-sum-atom.fq       pass
mask-atom.fq             pass
samples-atom.fq          pass 

test00.c                 pass

*)

let subs_kvar_to_strs state ?(suffix = "") subs kvar =
  let kv = symbol_to_armc kvar in 
  let scope = StrMap.find kv state.kv_scope in
  let scope_set = strlist_to_strset scope in
  let subs_map = subs_to_map subs in
  let kvar_str = 
    Printf.sprintf "%s(%s)" kv
      (List.map 
	 (fun v ->
	   let v_cap = String.capitalize v in
	   let v_cap_suffix = v_cap ^ suffix in
	   try 
	     match StrMap.find v subs_map with
	       | (Ast.Var s, _) -> 
		 let v_exp = var_to_armc s in
		 if StrSet.mem v_exp scope_set then v_cap_suffix
		 else v_exp
	       | _ -> v_cap_suffix
	   with Not_found -> v_cap
	 ) scope |> String.concat ", ") 
  in
  let subs_strs = 
    StrMap.fold (fun v e acc ->
      let subs_str = 
	Printf.sprintf "%s%s = %s" 
	  (String.capitalize v) suffix (StrMap.find v subs_map |> expr_to_armc)
      in
      match e with 
	| (Ast.Var s, _) -> 
	  let v_exp = var_to_armc s in
	  if StrSet.mem v_exp scope_set then subs_str :: acc
	  else acc
	| _ -> subs_str :: acc
    ) subs_map [] 
  in
  kvar_str, subs_strs

let mk_query_naming state = 
  List.map
    (fun kv ->
      Printf.sprintf "query_naming(%s(%s))." kv
	(StrMap.find kv state.kv_scope 
	    |> List.map 
		(fun v -> 
		  if 'a' <= v.[0] && v.[0] <= 'z' then v
		  else Printf.sprintf "'%s'" v
		) 
	    |> String.concat ", ")
    ) state.kvs |> String.concat "\n"

exception ValidClause
let horn_clause_to_tc state hc = 
  let head_str, head_grd_strs = 
(*
    match hc.head_kvars with
      | [(subs, kvar)] -> 
	let head_kvar_str, head_subs_strs = 
	  subs_kvar_to_strs state ~suffix:"_0" subs kvar 
	in
	head_kvar_str, head_subs_strs
      | [] -> 
	let head_pred = push_neg ~neg:true hc.head_pred |> simplify_tauto in
	"false", if P.is_tauto head_pred then [] else [pred_to_armc head_pred]
      | _ :: _ -> 
	print_horn_clause hc;
	failwith ("horn_clause_to_tc: unexpected clause " ^ hc.tag)
*)
    match P.is_tauto hc.head_pred, hc.head_kvars with
    | true, [(subs, kvar)] -> 
    let head_kvar_str, head_subs_strs = 
    subs_kvar_to_strs state ~suffix:"_0" subs kvar 
    in
    head_kvar_str, head_subs_strs
    | true, [] -> raise ValidClause
    | false, [] -> 
    let head_pred = push_neg ~neg:true hc.head_pred |> simplify_tauto in
    "false", if P.is_tauto head_pred then [] else [pred_to_armc head_pred]
    | _, _ -> 
    print_horn_clause hc;
    failwith ("horn_clause_to_tc: unexpected clause " ^ hc.tag)
  in 
  let tag_str = Printf.sprintf "id(%s)" hc.tag in
  let simple_body_pred = hc.body_pred |> push_neg ~neg:false |> simplify_tauto in
  let grd_tag_strs = 
    if P.is_tauto simple_body_pred then tag_str :: head_grd_strs
    else pred_to_armc simple_body_pred :: tag_str :: head_grd_strs
  in
  let body_strs, _ = 
    List.fold_left (fun (s, n) (subs, kvar) -> 
      let kvar_str, subs_strs = subs_kvar_to_strs state ~suffix:("_" ^ string_of_int n) subs kvar in
      kvar_str :: (subs_strs ++ s),
      n+1
    ) (grd_tag_strs, 1) hc.body_kvars
  in
  Printf.sprintf "%s :- %s.\n" head_str (body_strs |> List.rev |> String.concat ", ")

let to_qarmc out ts wfs =
  print_endline "Translating to QARMC.";
  
  print_endline "=========================";
  List.iter (Format.printf "%a" (C.print_t None)) ts;
  print_endline "=========================";

  let state = mk_kv_scope out ts wfs in
(*  let hcs = List.map (fun t -> t_to_horn_clause t |> simplify_horn_clause) ts in *)
  let hcs = List.map t_to_horn_clause ts in
  output_string out (mk_query_naming state);
  output_string out "\n\n";
  List.iter (fun hc -> 
    try horn_clause_to_tc state hc |> output_string out
    with ValidClause -> ()
  ) hcs;
  print_endline "heheheheh";
  List.iter (fun hc -> print_horn_clause hc; output_string out "\n") hcs
