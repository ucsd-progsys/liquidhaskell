(*
 * Copyright © 2009 The Regents of the University of California. All rights reserved. 
 *
 * Permission is hereby granted, without written agreement and without 
 * license or royalty fees, to use, copy, modify, and distribute this 
 * software and its documentation for any purpose, provided that the 
 * above copyright notice and the following two paragraphs appear in 
 * all copies of this software. 
 * 
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY 
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES 
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN 
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE. 
 * 
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, 
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS 
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION 
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONAst.Symbol.
 *
 *)

(* This module implements the IMP language and translation from fixpoint constraints *)


module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint
module Cg = FixConfig
(*module BS = BNstats*)

module Misc = FixMisc open Misc.Ops

(**********************************************************************)
(************* Datatypes for IMP Representation ***********************)
(**********************************************************************)

(* vars are always in lex order *)
(* We can have at most one set of temporaries in scope at a time
 * so we share names and mark temporaries *)

type var   = PVar of Sy.t
           | TVar of Sy.t

type kvar  = Ast.Subst.t * Sy.t

type decl  = RDecl of Sy.t * Sy.t list
           | PDecl of Sy.t

(* IMP commands *)

type tupl  = var list

type instr = Assm of A.pred list
           | Asst of A.pred list
           | Asgn of var * var
           | Rget of Sy.t * tupl
           | Rset of tupl * Sy.t
           | Havc of var

type block = instr list

type program = decl list * block list

(**********************************************************************)
(************* Datatypes for IMP Representation ***********************)
(**********************************************************************)

(* Convenience *)

let mk_temp = function
  | TVar v -> TVar v
  | PVar v -> TVar v

let rv_append v1 = function
  | TVar v2 | PVar v2 ->
      PVar (Sy.of_string (Sy.to_string v1 ^ "_" ^ Sy.to_string v2))
  
let collect_apps_from_pred p = 
  let apps = ref [] in
  let f_exp e =
    match E.unwrap e with
    | A.App (s, es) -> apps := (s, List.length es) :: !apps
    | t -> () in
  P.iter (fun _ -> ()) f_exp p; !apps

let collect_apps_from_instr = function
  | Assm ps
  | Asst ps ->
      Misc.flap collect_apps_from_pred ps
  | _ -> []

let collect_apps_from_block block =
  Misc.flap collect_apps_from_instr block

let collect_apps_from_program (_, blocks) =
  Misc.flap collect_apps_from_block blocks

(*************************************************************************)
(************* Rendering IMP to String ***********************************)
(*************************************************************************)

let print_var ppf = function 
  | PVar v -> F.fprintf ppf "%a" Sy.print v
  | TVar v -> F.fprintf ppf "'%a" Sy.print v

let print_tuple ppf =
  F.fprintf ppf "(%a)" (Misc.pprint_many false ", " print_var)

let print_instr ppf = function
  | Assm ps ->
      F.fprintf ppf "@[assume %a;@]" P.print (A.pAnd ps)
  | Asst ps ->
      F.fprintf ppf "@[assert %a;@]" P.print (A.pAnd ps)
  | Asgn (lhs, rhs) ->
      F.fprintf ppf "@[%a@ :=@ %a;@]" print_var lhs print_var rhs
  | Rget (rv, tupl) ->
      F.fprintf ppf "@[%a@ <|@ %a;@]" print_tuple tupl Sy.print rv
  | Rset (tupl, rv) ->
      F.fprintf ppf "@[%a@ |>@ %a;@]" print_tuple tupl Sy.print rv
  | Havc v ->
      F.fprintf ppf "@[havoc@ %a;@]" print_var v 

let print_decl ppf = function
  | RDecl (r, vs) ->
      F.fprintf ppf "@[rel@ (%a)@ (%a);@]" Sy.print r
        (Misc.pprint_many false ", " Sy.print) vs 
  | PDecl v ->
      F.fprintf ppf "@[var@ %a;@]" Sy.print v

let print_block ppf block =
  F.fprintf ppf "@[%a@]"
    (Misc.pprint_many false "\n" print_instr) block

let print_program ppf (decls, blocks) =
  F.fprintf ppf "@[%a@.%a@]"
    (Misc.pprint_many false "\n" print_decl) decls
    (Misc.pprint_many false "\n" print_block) blocks 

(* Printing as C syntax *)

let print_brel_as_c ppf = function
  | A.Eq -> F.fprintf ppf "=="
  | A.Ne -> F.fprintf ppf "!="
  | A.Gt -> F.fprintf ppf ">"
  | A.Ge -> F.fprintf ppf ">="
  | A.Lt -> F.fprintf ppf "<"
  | A.Le -> F.fprintf ppf "<="

let print_bop_as_c ppf = function
  | A.Plus  -> F.fprintf ppf "+"
  | A.Minus -> F.fprintf ppf "-"
  | A.Times -> F.fprintf ppf "*"
  | A.Div   ->  F.fprintf ppf "/"
  
let rec print_predicate_as_c ppf pred =
  match P.unwrap pred with
  | A.True ->
      F.fprintf ppf "True"
  | A.False ->
      F.fprintf ppf "False"
  | A.Atom (e1, r, e2) ->
      F.fprintf ppf "(%a %a %a)" print_expr_as_c e1 print_brel_as_c r print_expr_as_c e2
  | A.And ps ->
      Misc.pprint_many false " && " P.print ppf ps
  | A.Or ps ->
      Misc.pprint_many false " || " P.print ppf ps
  | A.Not p ->
      F.fprintf ppf "!(%a)" print_predicate_as_c p
  | A.Imp (p1, p2) ->
      print_predicate_as_c ppf (A.pOr [A.pNot p1; p2])
  | A.Iff (p1, p2) ->
      print_predicate_as_c ppf (A.pAnd [A.pImp (p1, p2); A.pImp (p2, p1)])
  | A.Bexp e ->
      print_expr_as_c ppf e
  | A.Forall (ds, p) ->
      assert false
      
and print_expr_as_c ppf expr =
  match E.unwrap expr with
  | A.Con c ->
      F.fprintf ppf "%a" A.Constant.print c
  | A.Var v ->
      F.fprintf ppf "%a" Sy.print v
  | A.App (f, es) ->
      F.fprintf ppf "%a(%a)" Sy.print f
        (Misc.pprint_many false ", " print_expr_as_c) es
  | A.Bin (e1, op, e2) ->
      F.fprintf ppf "(%a %a %a)"
        print_expr_as_c e1
        print_bop_as_c op
        print_expr_as_c e2
  | A.Ite (p, e1, e2) ->
      F.fprintf ppf "(%a ? %a : %a)"
        print_predicate_as_c p
        print_expr_as_c e1
        print_expr_as_c e2
  | A.Fld (s, e) ->
      print_expr_as_c ppf (A.eApp (Sy.of_string ("field" ^ Sy.to_string s), [e]))
(*  | A.Mod (e1, i) ->
      F.fprintf ppf "(%a mod %d)" print_expr_as_c e1 i 
*)

let print_var_as_c ppf = function
  | PVar v -> F.fprintf ppf "%a" Sy.print v
  | TVar v -> F.fprintf ppf "_%a" Sy.print v

let sy_append v1 v2 =
  Sy.of_string ((Sy.to_string v1) ^ "_" ^ (Sy.to_string v2))

let print_decl_as_c ppf = function
  | RDecl (rv, tupl) ->
      let pv v1 = (fun v2 -> F.fprintf ppf "@[int %a;@]@\n" Sy.print (sy_append v1 v2)) in
      List.iter (pv rv) tupl
  | PDecl v ->
      F.fprintf ppf "@[int %a;@]@\n" Sy.print v

let rec print_instr_as_c ppf = function
  | Havc v ->
      F.fprintf ppf "@[%a = nondet();@]" print_var_as_c v
  | Asgn (v1, v2) ->
      F.fprintf ppf "@[%a = %a@]" print_var_as_c v1 print_var_as_c v2
  | Assm ps ->
      F.fprintf ppf "@[if (!(%a)) { diverge(); }@]" print_predicate_as_c (A.pAnd ps)
  | Asst ps ->
      F.fprintf ppf "@[if (!(%a)) { error(); }@]" print_predicate_as_c (A.pAnd ps)
  | Rget (rv, tupl) ->
      List.map (fun v -> Asgn (mk_temp v, rv_append rv v)) tupl |>
      print_block_as_c ppf
  | Rset (tupl, rv) ->
      List.map (fun v -> Asgn (rv_append rv v, mk_temp v)) tupl |>
      print_block_as_c ppf

and print_block_as_c ppf block =
  F.fprintf ppf "@[%a@]"
    (Misc.pprint_many false "\n" print_instr_as_c) block

let print_list ppf = List.iter (F.fprintf ppf "%s")

let generate_uf (name, numargs) =
  let rec mkargs n s =
    if numargs > 0 then
      mkargs (n-1) ("int, " ^ s)
    else
      s in
  "int " ^ (Sy.to_string name) ^ "(" ^ (mkargs (numargs-1) "int") ^ ") {}"

let prologue =
  [ "void error() { ERROR: goto ERROR; }"
  ; "void diverge() { DIV: goto DIV; }"
  ; "int nondet() { int x; return x; }"
  ; "int main() {"
  ]

let epilogue =
  ["return 0; }"]

let print_program_as_c ppf ((decls, blocks) as program) =
  F.fprintf ppf "@[%a@.%a@.%a@.%a@.%a@.@]"
    print_list (collect_apps_from_program program |> List.map generate_uf)
    print_list prologue
    (Misc.pprint_many false "\n" print_decl_as_c) decls
    (Misc.pprint_many false "\n" print_block_as_c) blocks
    print_list epilogue

let check_imp (decls, instrs) = true
(* Translation from fixpoint to IMP *)

(*************************************************************************)
(************* Converting FixConfig.deft to SMTLIB ***********************)
(*************************************************************************)

(* Declarations *)

let filter_wfs cs =
  (* Misc.maybe_list (List.map (function Cg.Wfc x -> Some x | _ -> None) cs) *)
  Misc.map_partial (function Cg.Wfc x -> Some x | _ -> None) cs

let filter_subt cs =
  Misc.map_partial (function Cg.Cst x -> Some x | _ -> None) cs
  (* Misc.maybe_list (List.map (function Cg.Cst x -> Some x | _ -> None) cs)
   *)

let wf_to_decls wf =
  let vars  = wf |> C.env_of_wf
                 |> C.bindings_of_env
                 |> List.map fst
                 |> Misc.sort_and_compact
  in
  let kvars = C.kvars_of_reft (C.reft_of_wf wf) in
  ( List.map (fun k -> RDecl (snd k, vars)) kvars
  , List.map (fun v -> PDecl v) vars)

let constraints_to_decls cs =
  let decls = List.map wf_to_decls (filter_wfs cs) in
  let (rdecls, pdecls) = (Misc.flap fst decls, Misc.flap snd decls) in
  rdecls @ pdecls 

(* Constraint translation *)

let rec get_kdecl kvar decls =
  match decls with  
  | RDecl (k, vars) :: decls ->
      if k = kvar then
        vars
      else
        get_kdecl kvar decls
  | _ :: decls -> get_kdecl kvar decls
  | [] -> raise Not_found

let sub_to_assume (var, expr) =
  Assm [A.pAtom (A.eVar var, A.Eq, expr)]

(* [[{t | p}]]_get *)

let get_instrs vv decls (subs, kvar) =
  let vars = get_kdecl kvar decls |> List.map (fun v -> TVar v) in
  let assumes = subs |> Ast.Subst.to_list |> List.map sub_to_assume in
  Rget (kvar, vars) :: assumes @
  [Asgn (PVar vv, List.hd vars)]

let set_instr decls (subs, kvar) =
  Rset (List.map (fun v -> TVar v) (get_kdecl kvar decls), kvar)

let emptySol = PredAbs.read PredAbs.empty

let reft_to_get_instrs decls reft =
  let vv = C.vv_of_reft reft in
  let kvars = C.kvars_of_reft reft in
  let preds = C.preds_of_reft emptySol reft in
  match (kvars, preds) with
  | ([], preds) -> Havc (PVar vv) :: Assm preds :: []
  | (kvars, []) -> Misc.flap (get_instrs vv decls) kvars
  | (kvars, preds) -> Misc.flap (get_instrs vv decls) kvars @ ([Assm preds])

(* [[{t | p}]]_set *)

let reft_to_set_instrs decls reft =
  let kvars = C.kvars_of_reft reft in
  let preds = C.preds_of_reft emptySol reft in
  match (kvars, preds) with
  | ([], preds) -> Asst preds :: []
  | (kvars, []) -> List.map (set_instr decls) kvars
  | (kvars, preds) -> List.map (set_instr decls) kvars @ [(Asst preds)]

(* [[x:T; G]] *)

let binding_to_instrs decls (var, reft) =
  reft_to_get_instrs decls reft @ [Asgn (PVar var, PVar (C.vv_of_reft reft))]

let envt_to_instrs decls envt =
  Misc.flap (binding_to_instrs decls) (C.bindings_of_env envt)

let constraint_to_block decls c =
  let (env, grd, lhs, rhs) =
    (C.env_of_t c, C.grd_of_t c, C.lhs_of_t c, C.rhs_of_t c) in
  Assm [grd] ::
  envt_to_instrs decls env @
  reft_to_get_instrs decls lhs @
  reft_to_set_instrs decls rhs

let constraints_to_blocks decls cs =
  List.map (constraint_to_block decls) (filter_subt cs)

let mk_program cs =
  let decls = constraints_to_decls cs in
  (decls, constraints_to_blocks decls cs)

(* API *)
let render ppf cs = 
  cs |> mk_program 
     |> F.fprintf ppf "%a" print_program_as_c 
