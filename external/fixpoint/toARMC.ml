(* translation to ARMC *)

module C  = FixConstraint
module StrMap = Map.Make (struct type t = string let compare = compare end)
module StrSet = Set.Make (struct type t = string let compare = compare end)
module Misc = FixMisc open Misc.Ops


(* Andrey: TODO get rid of grd in t? grd p is a binding v:{v:b|p} *)
(* Andrey: TODO move to fixConstraint.ml? *)


(* Andrey: TODO move to ast.ml? *)
let pred_is_atomic (p, _) =
  match p with
    | Ast.True | Ast.False | Ast.Bexp _ | Ast.Atom _ -> true
    | Ast.And _ | Ast.Or _ | Ast.Not _ | Ast.Imp _ | Ast.Forall _ -> false

(* 
let negate_brel = function
  | Ast.Eq -> Ast.Ne
  | Ast.Ne -> Ast.Eq
  | Ast.Gt -> Ast.Le
  | Ast.Ge -> Ast.Lt
  | Ast.Lt -> Ast.Ge
  | Ast.Le -> Ast.Gt

let deep_negate_pred (p, t) =
  match p with
    | Ast.True -> Ast.pFalse
    | Ast.False -> Ast.pTrue
    | Ast.Atom (e1, r, e2) -> Ast.pAtom (e1, negate_brel r, e2)
    | _ -> Ast.pNot (p, t)
*)

let start_pc = "start"
let loop_pc = "loop"
let error_pc = "error"
let val_vname = "VVVV"
let card_vname = "CARD"
let exists_kv = "EX"
let primed_suffix = "p"
let str__cil_tmp = "__cil_tmp"

type kv_scope = {
  kvs : string list;
  kv_scope : string list StrMap.t
}

let sanitize_symbol s = 
  Str.global_replace (Str.regexp "@") "_at_"  s |> Str.global_replace (Str.regexp "#") "_hash_" 

let symbol_to_armc s = Ast.Symbol.to_string s |> sanitize_symbol

let mk_data_var ?(suffix = "") kv v = 
  Printf.sprintf "_%s_%s%s%s" 
    (sanitize_symbol kv) (sanitize_symbol v) (if suffix = "" then "" else "_") suffix

let constant_to_armc = Ast.Constant.to_string
let bop_to_armc = function 
  | Ast.Plus  -> "+"
  | Ast.Minus -> "-"
  | Ast.Times -> "*"
  | Ast.Div   -> "/"
let brel_to_armc = function 
  | Ast.Eq -> "="
  | Ast.Ne -> "=\\="
  | Ast.Gt -> ">" (*  ">= 1+" *)
  | Ast.Ge -> ">="
  | Ast.Lt -> "<" (*  "+1 =<" *)
  | Ast.Le -> "=<"
let bind_to_armc (s, t) = (* Andrey: TODO support binders *)
  Printf.sprintf "%s:%s" (symbol_to_armc s) (Ast.Sort.to_string t |> sanitize_symbol)
let rec expr_to_armc (e, _) = 
  match e with
    | Ast.Con c -> constant_to_armc c
    | Ast.Var s -> mk_data_var exists_kv (symbol_to_armc s)
    | Ast.App (s, es) ->
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
and pred_to_armc (p, _) = 
  match p with
    | Ast.True -> "1=1"
    | Ast.False -> "0=1"
    | Ast.Bexp e -> expr_to_armc e
    | Ast.Not p -> Printf.sprintf "neg(%s)" (pred_to_armc p) 
    | Ast.Imp (p1, p2) -> Printf.sprintf "(neg(%s); %s)" (pred_to_armc p1) (pred_to_armc p2)
    | Ast.And [] -> "1=1"
    | Ast.And [p] -> pred_to_armc p
    | Ast.And (_::_ as ps) -> Printf.sprintf "(%s)" (List.map pred_to_armc ps |> String.concat ", ")
    | Ast.Or [] -> "0=1"
    | Ast.Or [p] -> pred_to_armc p
    | Ast.Or (_::_ as ps) -> Printf.sprintf "(%s)" (List.map pred_to_armc ps |> String.concat "; ")
    | Ast.Atom (e1, r, e2) ->
	Printf.sprintf "%s %s %s" 
          (expr_to_armc e1) (brel_to_armc r) (expr_to_armc e2)
    | Ast.Forall (qs,p) -> (* Andrey: TODO support forall *) 
	Printf.sprintf "forall([%s], %s)" 
          (List.map bind_to_armc qs |> String.concat ", ") 
	  (pred_to_armc p)


let mk_kv_scope out ts wfs =
  output_string out "% kv -> scope:\n";
  let kvs = List.map C.kvars_of_t ts |> List.flatten |> List.map snd
    |> List.map symbol_to_armc |> Misc.sort_and_compact in
  let kv_scope =
    List.fold_left
      (fun m wf ->
	   match C.reft_of_wf wf |> C.ras_of_reft with
	     | [C.Kvar([], kvar)] ->
		 let v = symbol_to_armc kvar in
		 let scope = 
		   card_vname :: val_vname ::
		     (C.env_of_wf wf |> C.bindings_of_env |> List.map fst |> List.map symbol_to_armc
		     |> List.filter (fun s -> not (Misc.is_prefix str__cil_tmp s)) |> List.sort compare) in
		   Printf.fprintf out "%% %s -> %s\n"
		     v (String.concat ", " scope);
		   StrMap.add v scope m
	     | _ ->  (* Andrey: TODO print ill-formed wf *)
		 failure "ERROR: kname_scope_map: ill-formed wf"
      ) StrMap.empty wfs in
    {kvs = kvs; kv_scope = kv_scope}

let mk_data ?(suffix = "") ?(skip_kvs = []) s = 
  Printf.sprintf "[%s]"
    (List.map 
       (fun kv ->
	  try 
	    StrMap.find kv s.kv_scope |> 
		List.map (mk_data_var ~suffix:(if List.mem kv skip_kvs then "" else suffix) kv)
	  with Not_found -> failure "ERROR: rel_state_vs: scope not found for %s" kv
       ) s.kvs |> List.flatten |> String.concat ", ")

let mk_var2names state = 
  List.map
    (fun kv ->
       List.map 
	 (fun v -> 
	    Printf.sprintf "(%s, \'%s_%s\')"
	      (mk_data_var kv v)  kv v
	 ) (StrMap.find kv state.kv_scope) |> String.concat ", "
    ) state.kvs |> String.concat ", "

let mk_skip_update state kvs = 
  if kvs = [] then "1=1" else
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
    | card :: value :: data -> card, value, data
    | _ -> failure "ERROR: split_scope: empty scope %s" (String.concat ", " scope)

let reft_to_armc ?(suffix = "") state reft = 
  let vv = C.vv_of_reft reft |> symbol_to_armc in
  let rs = C.ras_of_reft reft in
    if rs = [] then "1=1" else
      List.map
	(function
	   | C.Conc pred -> pred_to_armc pred
	   | C.Kvar (subs, sym) -> 
	       let subs_map = List.fold_left
		 (fun m (s, e) -> StrMap.add (symbol_to_armc s) e m) StrMap.empty subs in
	       let find_subst v default = 
		 try StrMap.find v subs_map |> expr_to_armc with Not_found -> default in
	       let kv = symbol_to_armc sym in
	       let card, value, data = StrMap.find kv state.kv_scope |> split_scope in
		 Printf.sprintf "%s = 1" (mk_data_var ~suffix:suffix  kv card) 
		 :: Printf.sprintf "%s = %s" 
		   (mk_data_var ~suffix:suffix kv value) 
		   (find_subst vv (mk_data_var exists_kv vv)) 
		 :: List.map
		   (fun v -> 
		      Printf.sprintf "%s = %s"
			(mk_data_var ~suffix:suffix kv v)
			(find_subst v (mk_data_var exists_kv v))
		   ) data |> String.concat ", "
	) rs |> String.concat ", "

let mk_rule from_pc from_data to_pc to_data annot_guards annot_updates id = 
(*
  let unless_error l = if to_pc = error_pc then to_pc else l in
  let from_pc, to_pc = 
    if id = "t_init" then
      from_pc, unless_error "l0"
    else if List.mem id ["11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"; "19"] then
      "l0", unless_error "l1"
    else if List.mem id ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "20"; "21"; "22"; "23"; "24"; "25"; "26"; "27"; "28"] then
      "l1", unless_error "l1"
    else if List.mem id ["29"; "30"; "31"; "32"; "33"; "34"; "35"; "36"; "37"; "38"; "39"; "40"; "41"; "42"; "43"; "44"; "45"] then
      "l1", unless_error "l2"
    else
      "l2", unless_error "l2"
  in
*)
  let rec annot_conj_to_armc = function
    | (g, a) :: rest -> 
	if rest = [] then Printf.sprintf "\n   %s \t%% %s\n  ]," g a
	else Printf.sprintf "\n   %s, \t%% %s%s" g a (annot_conj_to_armc rest)
    | [] -> "],"
  in
    Printf.sprintf
      "
r(p(pc(%s), data(%s)), 
  p(pc(%s), data(%s)),
  [%s
  [%s
  %s).
" 
      from_pc from_data to_pc to_data
      (annot_conj_to_armc annot_guards)
      (annot_conj_to_armc annot_updates)
      id

let t_to_armc from_data to_data state t = 
  let grd = C.grd_of_t t in
  let lhs = C.lhs_of_t t in
  let rhs = C.rhs_of_t t in
  let rhs_s = C.reft_to_string rhs in
  let tag = try string_of_int (C.id_of_t t) with _ -> 
    failure "ERROR: t_to_armc: anonymous constraint %s" (C.to_string t) in
  let annot_guards = 
    List.map
      (fun (bv, reft) ->
	 reft_to_armc state (C.theta [(C.vv_of_reft reft, Ast.eVar bv)] reft),
	 C.binding_to_string (bv, reft)
      ) (C.env_of_t t |> C.bindings_of_env) 
    ++ [(pred_to_armc grd, Ast.Predicate.to_string grd); 
	(reft_to_armc state lhs, "|- " ^ (C.reft_to_string lhs))] in
  let ps, kvs =  
    List.fold_left (fun (ps', kvs') refa ->
		      match refa with
			| C.Conc p -> p::ps', kvs'
			| C.Kvar (subs, sym) -> ps', (subs, sym)::kvs'
		   ) ([], []) (C.ras_of_reft rhs) in
    (if ps <> [] then
       [mk_rule loop_pc from_data error_pc to_data annot_guards 
	  [(Ast.pAnd ps |> Ast.pNot |> pred_to_armc, "<: " ^ rhs_s)]
	  tag]
     else 
       [])
    ++
      (List.map 
	 (fun (_, sym) ->
	    let kv = symbol_to_armc sym in
	    let skip_kvs = List.filter (fun kv' -> kv <> kv') state.kvs in
	      mk_rule loop_pc from_data loop_pc 
		(mk_data ~suffix:primed_suffix ~skip_kvs:skip_kvs state)
		annot_guards 
		[(reft_to_armc ~suffix:primed_suffix state rhs, "<: " ^ rhs_s)]
		tag
	 ) kvs)

let to_armc out ts wfs =
  print_endline "Translating to ARMC.";
  let state = mk_kv_scope out ts wfs in
  let from_data =  mk_data state in
  let to_data = mk_data ~suffix:primed_suffix state in
    Printf.fprintf out
      ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,cube_size/1,start/1,error/1,refinement/1,cutpoint/1,invgen_template/2,invgen_template/1,cfg_exit_relation/1,stmtsrc/2,strengthening/2.

refinement(inter).
cube_size(1).

start(pc(%s)).
error(pc(%s)).
cutpoint(pc(%s)).

preds(p(_, data(%s)), [%s]).

trans_preds(p(_, data(%s)), p(_, data(%s)), []).

var2names(p(_, data(%s)), [%s]).
"
      start_pc error_pc loop_pc 
      from_data (List.map (fun kv ->
			     let card, _, _ = StrMap.find kv state.kv_scope |> split_scope in
			     let kv_card = mk_data_var kv card in
			       Printf.sprintf "%s = 0, %s = 1" kv_card kv_card
			  ) state.kvs |> String.concat ", ") (* preds *)
      from_data to_data (* trans_preds *)
      from_data (mk_var2names state); (* var2names *)
    output_string out 
      (mk_rule start_pc from_data loop_pc to_data [] 
	 [(List.map 
	     (fun kv -> 
		let card, _, _ = StrMap.find kv state.kv_scope |> split_scope in
		  Printf.sprintf "%s = 0" (mk_data_var ~suffix:primed_suffix kv card)
	     ) state.kvs |> String.concat ", ", 
	   "")]
         "t_init");
    List.iter (fun t -> t_to_armc from_data to_data state t |> List.iter (output_string out)) ts


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
