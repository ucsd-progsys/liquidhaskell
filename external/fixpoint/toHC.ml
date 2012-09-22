(* translation to HC'ARMC *)


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


let armc_true = "1=1"
let armc_false = "0=1"
(*
let armc_true = "true"
let armc_false = "false"
*)
let loop_pc = "loop"
let start_pc = "start"
let error_pc = "error"
let val_vname = "AA_0"
let card_vname = "CARD"
let exists_kv = "EX"
let primed_suffix = "p"
let str__cil_tmp = "__cil_tmp"

type kv_scope = {
  kvs : string list;
  kv_scope : string list StrMap.t;
  sol : Ast.pred list Sy.SMap.t;
}

type horn_clause = {
  body_pred : Ast.pred;
  body_kvars : (Su.t * Sy.t) list;
  head_pred : Ast.pred;
  head_kvar_opt : (Su.t * Sy.t) option;
  tag : string;
}

let sanitize_symbol s = 
  Str.global_replace (Str.regexp "@") "_at_"  s |> Str.global_replace (Str.regexp "#") "_hash_" |>
      Str.global_replace (Str.regexp "\\.") "_dot_" |> Str.global_replace (Str.regexp "'") "_q_" 

let symbol_to_armc s = Sy.to_string s |> sanitize_symbol

let mk_data_var ?(suffix = "") kv v = 
  Printf.sprintf "_%s_%s%s%s" 
    (sanitize_symbol v) (sanitize_symbol kv) (if suffix = "" then "" else "_") suffix

let mk_data ?(suffix = "") ?(skip_kvs = []) s = 
  Printf.sprintf "[%s]"
    (List.map 
       (fun kv ->
	  try 
	    StrMap.find kv s.kv_scope |> 
		List.map (mk_data_var ~suffix:(if List.mem kv skip_kvs then "" else suffix) kv)
	  with Not_found -> failure "ERROR: rel_state_vs: scope not found for %s" kv
       ) s.kvs |> List.flatten |> String.concat ", ")

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
let rec expr_to_armc expr = 
  let e = E.unwrap expr in
    match e with
      | Ast.Con c -> constant_to_armc c
      | Ast.Var s -> mk_data_var exists_kv (symbol_to_armc s)
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
      | _ -> failwith (Printf.sprintf "expr_to_armc: %s" (E.to_string expr))
and pred_to_armc pred = 
  let p = P.unwrap pred in 
    match p with
      | Ast.True -> armc_true
      | Ast.False -> armc_false
      | Ast.Bexp e -> Printf.sprintf "%s = 1" (expr_to_armc e)
      | Ast.Not (Ast.True, _) -> armc_false
      | Ast.Not (Ast.False, _) -> armc_true
      | Ast.Not p -> Printf.sprintf "neg(%s)" (pred_to_armc p) 
      | Ast.Imp (p1, p2) -> Printf.sprintf "imp(%s, %s)" (pred_to_armc p1) (pred_to_armc p2)
      | Ast.And [] -> armc_true
      | Ast.And [p] -> pred_to_armc p
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

let preds_kvars_of_reft reft =
  List.fold_left 
    (fun (ps, ks) r ->
       match r with
	 | C.Conc p -> p :: ps, ks
	 | C.Kvar (subs, kvar) -> ps, (subs, kvar) :: ks
    ) ([], []) (C.ras_of_reft reft)

let preds_to_pred ps =
  match ps with 
    | [] -> Ast.pTrue
    | [p] -> p
    | _ :: _ -> Ast.pAnd ps	 

let rec flatten_pAnd pred =
  match P.unwrap pred with
    | Ast.And [] -> []
    | Ast.And [p] -> flatten_pAnd p
    | Ast.And ps -> List.map flatten_pAnd ps |> List.flatten
    | _ -> [pred]

let t_to_horn_clause t =
  let lhs_ps, lhs_ks = C.lhs_of_t t |> preds_kvars_of_reft in
  let body_ps, body_ks = 
    Sy.SMap.fold 
      (fun bv reft (ps, ks) -> 
	 let ps', ks' = preds_kvars_of_reft (C.theta (Su.of_list [(C.vv_of_reft reft, Ast.eVar bv)]) reft) in
	   List.rev_append ps' ps, List.rev_append ks' ks
      ) (C.env_of_t t) (C.grd_of_t t :: lhs_ps, lhs_ks) in
  let head_ps, head_ks = C.rhs_of_t t |> preds_kvars_of_reft in
  let head_kvar_opt =
    match head_ks with 
      | [] -> None
      | [head_kvar] -> Some head_kvar
      | _ ->
	  failwith (Printf.sprintf "t_to_horn_clause: multiple k's in rhs of %d" (C.id_of_t t));
  in
    {
      body_pred = Ast.pAnd body_ps |> flatten_pAnd |> preds_to_pred; 
      body_kvars = body_ks; 
      head_pred = Ast.pAnd head_ps |> flatten_pAnd |> preds_to_pred;
      head_kvar_opt = head_kvar_opt;
      tag = C.id_of_t t |> string_of_int;
    }

let horn_clause_to_string hc = 
  Printf.sprintf "%s: %s, %s :- %s, %s."
    hc.tag 
    (P.to_string hc.head_pred)
    (match hc.head_kvar_opt with
       | Some (subs, kvar) -> C.refa_to_string (C.Kvar (subs, kvar))
       | None -> "none"
    )
    (P.to_string hc.body_pred)
    (List.map (fun (subs, kvar) -> C.refa_to_string (C.Kvar (subs, kvar))) hc.body_kvars |> String.concat ", ")


module CFGNodeSet = Set.Make (struct type t = StrSet.t let compare = StrSet.compare end)


module DepV = struct
  type t = string
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module DepE = struct
  type t = string
  let compare = Pervasives.compare
  let default = ""
end
module DepG = Graph.Persistent.Digraph.ConcreteLabeled(DepV)(DepE)

module Display = struct
  include DepG
  let vertex_name v = DepG.V.label v
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end
module DepGToDot = Graph.Graphviz.Dot(Display)
module DepGOper = Graph.Oper.P(DepG)

module DepGSCC = Graph.Components.Make(DepG)

module G = Graph.Pack.Digraph

let hc_to_dep hc =
  (match hc.head_kvar_opt with
     | Some (_, sym) -> Some (symbol_to_armc sym) 
     | None -> None
  ),
  List.map (fun (_, sym) -> symbol_to_armc sym) hc.body_kvars |> List.sort compare

(*
let mk_cfg state hcs =
  let nodes = ref (CFGNodeSet.singleton StrSet.empty) in
  let nodes_size = ref 0 in
  let nodes_size' = ref 1 in
    while !nodes_size < !nodes_size' do
      nodes_size := CFGNodeSet.cardinal !nodes;
      List.iter (fun hc ->
		   let heads, body = hc_to_dep hc in
		   let body_set = List.fold_left (fun sofar b -> StrSet.add b sofar) StrSet.empty body in
		     List.iter (fun node ->
				  List.iter (fun head ->
					       if StrSet.subset body_set node then
						 nodes := CFGNodeSet.add (StrSet.add head node) !nodes
					    ) heads
			       ) (CFGNodeSet.elements !nodes)
		) hcs;
      nodes_size' := CFGNodeSet.cardinal !nodes
    done;
    Printf.printf "nodes: %s\n" (List.sort compare state.kvs |> String.concat ", ");
    CFGNodeSet.iter (fun node -> 
		       Printf.printf "node: %s\n" (StrSet.elements node |> List.sort compare |> String.concat ", ")
		    ) !nodes;
    let g = G.create () in
      List.iter (fun hc -> 
		   let heads, body = hc_to_dep hc in
		     List.iter (fun b -> 
				  List.iter (fun head -> 
					       G.add_edge g (G.V.create 1) (G.V.create 2)
					    ) heads
			       ) body
		) hcs;
    let depg = 
      List.fold_left
	(fun g hc -> 
	   let heads, body = hc_to_dep hc in
	     List.fold_left 
	       (fun g' b -> 
		  List.fold_left 
		    (fun g'' head -> 
		       DepG.add_edge_e g'' (DepG.E.create b (* hc.tag *) "" head)
		    ) g' heads
	       ) g body
	) DepG.empty hcs in
    let dep_cs = 
      List.fold_left
	(fun g hc -> 
	   let heads, _ = hc_to_dep hc in
	     List.fold_left 
	       (fun g' hc' -> 
		  (* check if heads intersect body' *)
		  let _, body' = hc_to_dep hc' in
		    if hc.tag <> hc'.tag && List.exists (fun head -> List.mem head body') heads then 
		      DepG.add_edge g' hc.tag hc'.tag
		    else 
		      g'
	       ) g hcs
	) DepG.empty hcs in
    let out = open_out "/var/tmp/awesome/g.dot" in
      DepGToDot.output_graph out depg;
      close_out out;
    let out = open_out "/var/tmp/awesome/t.dot" in
      DepGToDot.output_graph out (DepGOper.transitive_closure depg);
      close_out out;
    let out = open_out "/var/tmp/awesome/cs.dot" in
      DepGToDot.output_graph out dep_cs;
      close_out out
*)
    

let kvar_to_hc_armcs ?(suffix = "") state (subs, sym) = 
  let subs_map = List.fold_left (fun m (s, e) -> StrMap.add (symbol_to_armc s) e m) StrMap.empty (Su.to_list subs) in
  let find_subst v default = try StrMap.find v subs_map |> expr_to_armc with Not_found -> default in
  let kv = symbol_to_armc sym in
    try
      let scope = StrMap.find kv state.kv_scope in 
	Printf.sprintf "%s(%s)" 
	  kv (List.map (mk_data_var ~suffix:suffix kv) scope |> String.concat ", ")
	:: List.map (fun v -> 
		       Printf.sprintf "%s = %s" 
			 (mk_data_var ~suffix:suffix kv v) (find_subst v (mk_data_var exists_kv v))
		    ) scope 
    with Not_found -> [armc_true] (* input variable *)

let kvar_to_armcs ?(suffix = "") ?(with_card=true) state (subs, sym) = 
  let subs_map = 
    List.fold_left (fun m (s, e) -> StrMap.add (symbol_to_armc s) (expr_to_armc e) m) StrMap.empty (Su.to_list subs) in
  let find_subst v default = try StrMap.find v subs_map with Not_found -> default in
  let kv = symbol_to_armc sym in
  try
    let scope = StrMap.find kv state.kv_scope in
    let card_armc, data = 
      if with_card then
	[Printf.sprintf "%s = 1" (mk_data_var ~suffix:suffix kv card_vname)], List.tl scope
      else 
	[], scope
    in
      card_armc
      @ List.map (fun v -> 
		     Printf.sprintf "%s = %s" 
		       (mk_data_var ~suffix:suffix kv v) (find_subst v (mk_data_var exists_kv v))
		  ) data |> String.concat ", "
  with Not_found -> armc_true (* input variable *)

let hc_to_rule state hc =
  let mk_rule head body tag = Printf.sprintf "rule(%s, %s, [%s])." tag head body in
  let body = 
    pred_to_armc hc.body_pred :: (List.map (kvar_to_hc_armcs state) hc.body_kvars |> List.flatten) |>  
	String.concat ", " in
  let prules = 
    if P.is_tauto hc.head_pred then []
    else [mk_rule error_pc  (Printf.sprintf "%s, %s" body (Ast.pNot hc.head_pred |> pred_to_armc)) hc.tag] in
  let krules =
    match hc.head_kvar_opt with
      | Some kvar ->
	 let head_armcs = kvar_to_hc_armcs ~suffix:primed_suffix state kvar in
	   [mk_rule 
	     (List.hd head_armcs) (* kv *)
	     (body :: (List.tl head_armcs (* subs *)) |> String.concat ", ")
	     hc.tag]
      | None -> []
  in
    krules @ prules

let mk_rule from_pc from_data to_pc to_data guard update tag = 
  Printf.sprintf "r(p(pc(%s), data(%s)),\np(pc(%s), data(%s)),\n[%s],\n[%s], %s).%s"
    from_pc from_data to_pc to_data guard update tag
    (if guard = "" && update = "" then Printf.sprintf "\nid_trans(%s)." tag else "")

let hc_to_armc ?(cfg=false) ?(with_card=true) ?(with_dataflow=false) state hc = 
  let from_data = mk_data state in
  let to_data = mk_data ~suffix:primed_suffix state in
  let body = pred_to_armc hc.body_pred :: List.map (kvar_to_armcs ~with_card:with_card state) hc.body_kvars in
  let body_kv_strs = hc_to_dep hc |> snd |> List.filter (fun kv -> StrMap.mem kv state.kv_scope) in
  let prules =
    if P.is_tauto hc.head_pred then []
    else 
      mk_rule 
	(if cfg then Printf.sprintf "src_%s" hc.tag else loop_pc)
	from_data error_pc to_data 
	((Ast.pNot hc.head_pred |> pred_to_armc) :: body |> String.concat ",\n") "" hc.tag
      :: 
	if with_dataflow then
	  [Printf.sprintf "dataflow_transition(%s, [%s], [])." hc.tag (String.concat ", " body_kv_strs)]
	else [] in
  let krules =
    match hc.head_kvar_opt with
      | Some ((subs, sym) as kvar) ->
	  let kv = symbol_to_armc sym in
	  let skip_kvs = List.filter (fun kv' -> kv <> kv') state.kvs in
	    mk_rule 
	      (if cfg then Printf.sprintf "src_%s" hc.tag else loop_pc)
	      from_data 
	      (if cfg then Printf.sprintf "dst_%s" hc.tag else loop_pc)
	      (mk_data ~suffix:primed_suffix ~skip_kvs:skip_kvs state) 
	      (body |> String.concat ",\n") 
	      (kvar_to_armcs ~with_card:with_card ~suffix:primed_suffix state kvar) 
	      hc.tag
	    ::
	      if with_dataflow then
		[Printf.sprintf "dataflow_transition(%s, [%s], [%s])." hc.tag (String.concat ", " body_kv_strs) kv]
	      else []
      | None -> []
  in
    krules @ prules

let mk_hc_var2names state = 
  List.map
    (fun kv ->
       Printf.sprintf "var2names(p(pc(%s), data(%s)), [%s])."
	 kv
	 (List.map (mk_data_var kv) (StrMap.find kv state.kv_scope) |> String.concat ", ")
	 (List.map 
	    (fun v -> 
	       Printf.sprintf "(%s, \'%s_%s\')" (mk_data_var kv v)  v kv
	    ) (StrMap.find kv state.kv_scope) |> String.concat ", ")
    ) state.kvs |> String.concat "\n"

let mk_var2names state = 
  Printf.sprintf "var2names(p(pc(_), data(%s)), [%s])."
    (mk_data state)
    (List.map
       (fun kv ->
	  List.map 
	    (fun v -> 
	       Printf.sprintf "(%s, \'%s_%s\')" (mk_data_var kv v)  v kv
	    ) (StrMap.find kv state.kv_scope) |> String.concat ", "
       ) state.kvs |> String.concat ", ")

let mk_hc_preds state = 
  List.map
    (fun kv ->
       Printf.sprintf "preds(p(pc(%s), data(%s)), [])."
	 kv
	 (List.map (mk_data_var kv) (StrMap.find kv state.kv_scope) |> String.concat ", ")
    ) state.kvs |> String.concat "\n"

let mk_preds ?(with_card = true) state = 
  let preds = 
    if with_card then
      List.map (fun kv ->
		  let card = StrMap.find kv state.kv_scope |> List.hd in
		  let kv_card = mk_data_var kv card in
		    Printf.sprintf "%s = 0, %s = 1" kv_card kv_card
	       ) state.kvs |> String.concat ", "
    else 
      ""
  in
    Printf.sprintf "preds(p(pc(_), data(%s)), [%s])." (mk_data state) preds

let mk_start_rule state = 
  mk_rule start_pc (mk_data state) loop_pc (mk_data ~suffix:primed_suffix state) "" 
    (List.map (fun kv ->
		 let card = StrMap.find kv state.kv_scope |> List.hd in
		   Printf.sprintf "%s = 0" (mk_data_var ~suffix:primed_suffix kv card)
	      ) state.kvs |> String.concat ", ")
    "start_t"

let find_kv_wf_scope wfs kv = 
  let wf =
    try List.find (fun wf -> 
		     match C.reft_of_wf wf |> C.kvars_of_reft with
		       | [(subs, kvar)] -> Su.is_empty subs && kv = symbol_to_armc kvar
		       | _ -> false
		  ) wfs 
    with Not_found -> failwith (Printf.sprintf "find_wf_scope: %s" kv)
  in
    Sy.SMap.fold (fun kvar _ sofar -> StrSet.add (symbol_to_armc kvar) sofar) (C.env_of_wf wf) StrSet.empty

(* map each k variable to variables in its scope *)
(* k variables no appearing in any rhs don't have any scope *)
let mk_kv_scope ?(with_card=true) ?(hcs=[]) out ts wfs sol =
  (*
  List.iter (fun wf -> 
	       let env = C.env_of_wf wf in
	       let bvs = Sy.SMap.fold (fun bv _ sofar -> symbol_to_armc bv :: sofar) env [] in
		 Printf.printf "wf: %s : %s\n" (C.reft_of_wf wf |> C.reft_to_string) (String.concat ", " bvs)
	    ) wfs;
  *)
  let hcs = if hcs = [] then List.map t_to_horn_clause ts else hcs in
  let hc_deps = List.map hc_to_dep hcs in
  let kv_scope_aux =
    ref (List.fold_left (fun kv_scope' t ->
			   (* collect bound vars of t *)
			   let scope =
			     Sy.SMap.fold (fun bv _ scope' ->
					     StrSet.add (symbol_to_armc bv) scope'
					  ) (C.env_of_t t) StrSet.empty in
			   let _, rhs_kvs = C.rhs_of_t t |> C.preds_kvars_of_reft in
			     (* add these bound vars to the scope of each k var in rhs of t *)
			     List.fold_left (fun kv_scope'' kv ->
					       StrMap.add kv (StrSet.union 
								(try StrMap.find kv kv_scope'' with Not_found -> StrSet.empty) 
								scope) kv_scope''
					    ) kv_scope' (List.map snd rhs_kvs |> List.map symbol_to_armc)
			) StrMap.empty ts) in
  let done_flag = ref false in
    (* if k' depends on k then scope(k') contains scope(k) *)
    while not(!done_flag) do
      done_flag := true;
      List.iter (fun (head_opt, body) ->
		   match head_opt with
		     | Some kv' -> 
			 let scope_kv' = StrMap.find kv' !kv_scope_aux in 
			 let size_scope_kv' = StrSet.cardinal scope_kv' in
			 let upd_scope_kv' = 
			   List.fold_left (fun sofar kv ->
					     StrSet.union (try StrMap.find kv !kv_scope_aux with Not_found -> StrSet.empty) sofar
					  ) scope_kv' body 
			 in
			   if size_scope_kv' < StrSet.cardinal upd_scope_kv' then
			     begin
			       kv_scope_aux := StrMap.add kv' upd_scope_kv' !kv_scope_aux;
			       done_flag := false
			     end
		     | None -> ()
		) hc_deps
    done;
    let kv_scope = 
      (* sort scope, add value variable and, if needed, cardinality variable *)
      StrMap.mapi (fun kv scope -> 
		     let scope' = val_vname :: (StrSet.inter scope (find_kv_wf_scope wfs kv) |> StrSet.elements |> List.sort compare) in
		       if with_card then card_vname :: scope' else scope'
		  ) !kv_scope_aux in
    let kvs = StrMap.fold (fun kv _ kvs -> kv :: kvs) kv_scope [] in
      StrMap.iter (fun kv scope ->
    		     Printf.fprintf out "%% %s -> %s\n" kv (String.concat ", " scope)) kv_scope;
      {kvs = kvs; kv_scope = kv_scope; sol = sol}


let to_horn out ts wfs sol =
  print_endline "Translating to Horn clauses.";
(*  let cex = [1;2;4;5;9;23;24] in   *)
  let cex = [] in
  let ts = if cex = [] then ts else List.filter (fun t -> List.mem (C.id_of_t t) cex) ts in
  let state = mk_kv_scope out ~with_card:false ts wfs sol in
    Printf.fprintf out
      ":- multifile rule/3, var2names/2, preds/2, error/1.

error(%s).
%s
%s
"
      error_pc
      (mk_hc_var2names state)
      (mk_hc_preds state);
    List.iter (fun t -> 
		 Printf.fprintf out "/*\n%s\n%s\n*/\n" (C.to_string t) (t_to_horn_clause t |> horn_clause_to_string);
		 List.iter (fun r -> 
			      output_string out r;
			      output_string out "\n\n"
			   ) (t_to_horn_clause t |> hc_to_rule state)
	      ) ts

let to_armc out ts wfs sol =
  print_endline "Translating to ARMC. ToHC.to_armc";
(*  let cex = [1;5;13;14;68;69;54] in *)
  let cex = [] in
  let state = mk_kv_scope out ts wfs sol in
    Printf.fprintf out
      ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,cube_size/1,start/1,error/1,refinement/1,cutpoint/1,invgen_template/2,invgen_template/1,cfg_exit_relation/1,stmtsrc/2,strengthening/2.
refinement(inter). 
cube_size(1). 

start(pc(%s)).
error(pc(%s)).
cutpoint(pc(%s)).
\n%s\n\n%s\n
"
      start_pc error_pc loop_pc 
      (mk_var2names state)
      (mk_preds state);
    Printf.fprintf out "%s\n\n" (mk_start_rule state);
    List.iter (fun t -> 
		 if List.mem (C.id_of_t t) cex || List.length cex = 0 then
		   let hc = t_to_horn_clause t in
		     Printf.fprintf out "/*\n%s%s\n*/\n" (C.to_string t) (horn_clause_to_string hc);
		     List.iter (fun r -> 
				  output_string out r;
				  output_string out "\n\n"
			       ) (hc_to_armc state hc)
		 else
		   ()
	      ) ts;
    List.iter (fun id ->  
		 List.iter (fun t -> 
			      if List.mem (C.id_of_t t) cex then
				Printf.printf "%s\n" (C.to_string t)
			   ) ts
	      ) cex


let to_dataflow_armc out ts wfs sol =
  print_endline "Translating to ARMC. ToHC.to_dataflow_armc ";
  let with_card_flag = false in
(*  let cex = [1;2;4;5;9;23;24] in   *)
  let cex = [] in
  let ts = (if cex = [] then ts else List.filter (fun t -> List.mem (C.id_of_t t) cex) ts) in
  let hcs = List.map t_to_horn_clause ts in
  let state = mk_kv_scope ~with_card:with_card_flag ~hcs:hcs out ts wfs sol in
    Printf.fprintf out
      ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,cube_size/1,start/1,error/1,refinement/1,cutpoint/1,invgen_template/2,invgen_template/1,cfg_exit_relation/1,stmtsrc/2,strengthening/2,id_trans/1,dataflow_transition/3.
refinement(inter). 
cube_size(1). 

start(pc(%s)).
error(pc(%s)).

\n%s\n\n%s\n
"
      start_pc error_pc 
      (mk_var2names state)
      (mk_preds ~with_card:with_card_flag state);
    (* connect the start with the loop *)
    Printf.fprintf out "%s\n\n" (mk_rule start_pc (mk_data state) loop_pc (mk_data state) "" "" "start");
    Printf.fprintf out "dataflow_transition(%s, [], []).\n\n" "start";
    List.iter
      (fun hc -> 
	 Printf.fprintf out "/*\n%s\n*/\n" (horn_clause_to_string hc);
	 (* the actual transition relation, each disjunct *) 
	 List.iter (Printf.fprintf out "%s\n\n") (hc_to_armc ~cfg:false ~with_card:with_card_flag ~with_dataflow:true state hc)
      ) hcs;
    output_string out "/*\n";
    List.iter (fun t -> Printf.fprintf out "%s\n" (C.to_string t)) ts;
    List.iter (fun hc -> Printf.fprintf out "%s\n\n" (horn_clause_to_string hc)) hcs;
    output_string out "*/\n"
