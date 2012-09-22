(* Dumping constraints as Horn clauses without any simplifications *)

module C  = FixConstraint
module Co = Constants 
module Sy = Ast.Symbol
module Su = Ast.Subst
module P = Ast.Predicate
module E = Ast.Expression
module StrMap = Map.Make (struct type t = string let compare = compare end)
module StrSet = Set.Make (struct type t = string let compare = compare end)
module Misc = FixMisc open Misc.Ops

let raw_true = "1=1"
let raw_false = "0=1"


let sanitize_symbol s = 
  Str.global_replace (Str.regexp "@") "_at_"  s |> Str.global_replace (Str.regexp "#") "_hash_" |>
      Str.global_replace (Str.regexp "\\.") "_dot_" |> Str.global_replace (Str.regexp "'") "_q_" 

let symbol_to_raw s = Sy.to_string s |> sanitize_symbol
let constant_to_raw = Ast.Constant.to_string
let bop_to_raw = function 
  | Ast.Plus  -> "+"
  | Ast.Minus -> "-"
  | Ast.Times -> "*"
  | Ast.Div   -> "/"
let brel_to_raw = function 
  | Ast.Eq -> "="
  | Ast.Ne -> "=\\="
  | Ast.Gt -> ">"
  | Ast.Ge -> ">="
  | Ast.Lt -> "<"
  | Ast.Le -> "=<"
let bind_to_raw (s, t) = (* Andrey: TODO support binders *)
  Printf.sprintf "%s:%s" (symbol_to_raw s) (Ast.Sort.to_string t |> sanitize_symbol)
let rec expr_to_raw expr = 
  let e = E.unwrap expr in
    match e with
      | Ast.Con c -> constant_to_raw c
      | Ast.Var s -> symbol_to_raw s
      | Ast.App (s, es) -> 
	  if !Co.purify_function_application then "_" else
	    let str = symbol_to_raw s in
	      if es = [] then str else
		Printf.sprintf "f_%s(%s)" str (List.map expr_to_raw es |> String.concat ", ")
      | Ast.Bin (e1, op, e2) ->
	  Printf.sprintf "(%s %s %s)" 
	    (expr_to_raw e1) (bop_to_raw op) (expr_to_raw e2)
      | Ast.Ite (ip, te, ee) -> 
	  Printf.sprintf "ite(%s, %s, %s)" 
	    (pred_to_raw ip) (expr_to_raw te) (expr_to_raw ee)
      | Ast.Fld (s, e) -> 
	  Printf.sprintf "fld(%s, %s)" (expr_to_raw e) (symbol_to_raw s) 
      | _ -> failwith (Printf.sprintf "expr_to_raw: %s" (E.to_string expr))
and pred_to_raw pred = 
  if P.is_tauto pred then 
    raw_true
  else 
    let p = P.unwrap pred in 
      match p with
	| Ast.True -> raw_true
	| Ast.False -> raw_false
	| Ast.Bexp e -> Printf.sprintf "%s = 1" (expr_to_raw e)
	| Ast.Not (Ast.True, _) -> raw_false
	| Ast.Not (Ast.False, _) -> raw_true
	| Ast.Not p -> Printf.sprintf "neg(%s)" (pred_to_raw p) 
	| Ast.Imp (p1, p2) -> Printf.sprintf "imp(%s, %s)" (pred_to_raw p1) (pred_to_raw p2)
	| Ast.And [] -> raw_true
	| Ast.And [p] -> pred_to_raw p
	| Ast.And (_::_ as ps) -> 
	    Printf.sprintf "(%s)" (List.map pred_to_raw ps |> String.concat ", ")
	| Ast.Or [] -> raw_false
	| Ast.Or [p] -> pred_to_raw p
	| Ast.Or (_::_ as ps) -> Printf.sprintf "(%s)" (List.map pred_to_raw ps |> String.concat "; ")
	| Ast.Atom (e1, Ast.Eq, (Ast.Ite(ip, te, ee), _)) ->
	    let ip_str = pred_to_raw ip in
	    let e1_str = expr_to_raw e1 in
	      Printf.sprintf "((%s, %s = %s); (neg(%s), %s = %s))"
		ip_str e1_str (expr_to_raw te) 
		ip_str e1_str (expr_to_raw ee) 
	| Ast.Atom (e1, r, e2) ->
	    Printf.sprintf "%s %s %s" 
              (expr_to_raw e1) (brel_to_raw r) (expr_to_raw e2)
	| Ast.Forall (qs,p) -> (* Andrey: TODO support forall *) 
	    Printf.sprintf "forall([%s], %s)" 
              (List.map bind_to_raw qs |> String.concat ", ") 
	      (pred_to_raw p)

let subst_to_raw subst =
  Misc.map_to_string
    (fun (sym, expr) ->
       Printf.sprintf "%s = %s" (symbol_to_raw sym) (expr_to_raw expr)
    ) (Ast.Subst.to_list subst)

let kvar_to_scope_tbl = Hashtbl.create 100

let wfs_option = ref None

let is_upper c = c = Char.uppercase c

let find_scope wfs sym =
  match Misc.map_partial 
    (fun wf -> 
       let reft = C.reft_of_wf wf in 
       let vv = C.vv_of_reft reft in
	 match C.ras_of_reft reft with
	   | [C.Kvar (subst, sym')] when (Ast.Subst.is_empty subst) && sym = sym' ->
	       let vv_raw = symbol_to_raw vv in
		 Some (vv_raw, 
		       StrSet.remove vv_raw
			 (Sy.SMap.fold (fun bv reft sofar ->
					  if not(C.sort_of_reft reft |> Ast.Sort.is_int)
(*					      is_upper (Sy.to_string bv).[0] *)
					  then 
					    sofar
					  else 
					    StrSet.add (symbol_to_raw bv) sofar
				       ) (C.env_of_wf wf) StrSet.empty))
	   | _ -> None
    ) wfs with
      | (vv, scope) :: _ -> vv, scope
      | [] -> failwith (Printf.sprintf "Not found wf constraint for %s" (Sy.to_string sym))

let scope_of_ksym ksym =  
  try
    Hashtbl.find kvar_to_scope_tbl ksym
  with Not_found ->
    begin
      match !wfs_option with
	| Some wfs -> 
	    let scope = find_scope wfs ksym in
	      Hashtbl.add kvar_to_scope_tbl ksym scope;
	      scope
	| None -> failwith "Uninitialized wfs_option reference"
    end

let refa_to_raw = function 
  | C.Conc pred -> pred_to_raw pred
  | C.Kvar (subst, sym) ->
      let vv, scope = scope_of_ksym sym in 
      let subs = Ast.Subst.to_list subst in
      let params =
	List.map (fun param ->
		    try
		      let _, exp =
			List.find (fun (v, _) -> 
				     symbol_to_raw v = param
				  ) subs in 
			match exp with 
			  | Ast.Var param', _ -> symbol_to_raw param'
			  | _ -> failwith (Printf.sprintf "substition by a non-variable %s" (E.to_string exp))
		    with Not_found -> param 
		 ) (vv :: (StrSet.elements scope |> List.sort compare))
      in
	Printf.sprintf "%s(%s)" (symbol_to_raw sym) (String.concat ", " params)

let reft_to_raw reft = 
  if C.sort_of_reft reft |> Ast.Sort.is_func then 
    raw_true
  else 
    let ras = C.ras_of_reft reft in
      match ras with
	| [] -> raw_true
	| _ :: _ ->
	    Misc.map_to_string refa_to_raw ras

let subst_refa refa sym exp = 
  match refa with 
    | C.Conc pred -> C.Conc (P.subst pred sym exp)
    | C.Kvar (subst, sym') -> C.Kvar (Ast.Subst.extend subst (sym, exp), sym')

let subst_reft reft sym exp =
  C.make_reft 
    (C.vv_of_reft reft) (C.sort_of_reft reft) 
    (List.map (fun refa -> subst_refa refa sym exp) (C.ras_of_reft reft))

let env_to_raw env =
  Sy.SMap.fold 
      (fun bv reft sofar -> 
	 [subst_reft reft (C.vv_of_reft reft) (Ast.eVar bv) |> reft_to_raw] ++ sofar
      ) env [] |> List.filter ((<>) "1=1") |> String.concat ", "


let c_to_raw c =
  Printf.sprintf "rule(%d, %s, [\n%s,\n%s,\n%s\n]).\n\n"
    (C.id_of_t c)
    (C.rhs_of_t c |> reft_to_raw)
    (C.lhs_of_t c |> reft_to_raw)
    (C.grd_of_t c |> pred_to_raw)
    (C.env_of_t c |> env_to_raw)

let to_raw_horn out cs wfs sol = 
  let cs = FixSimplify.simplify_ts cs in
    wfs_option := Some wfs;
    print_endline "Translating to raw Horn clauses.";
    List.iter (fun c -> 
		 Printf.fprintf out "/*\n%s*/\n" (C.to_string c);
		 output_string out (c_to_raw c)
	      ) cs
