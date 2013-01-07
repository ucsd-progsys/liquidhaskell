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
module So = A.Sort
module SM = Sy.SMap
module SS = Sy.SSet
module C  = FixConstraint
module Cg = FixConfig
(*module BS = BNstats*)

module Misc = FixMisc open Misc.Ops


(*************************************************************************)
(************* Datatypes for SMTLIB Representation ***********************)
(*************************************************************************)
(*
type sort = Int | Bool | Func of (sort list * sort)
*)
type rpred  
  = A.pred                      (* Bexp (App (k, es)) *) 

type vdef
  = Sy.t * So.t                 (* variable, sort *)

type kdef
  = Sy.t * (vdef list)

type cstr
  = { lhs : A.pred 
    ; rhs : rpred option
    ; id  : int 
    }

type smtlib 
  = { vars   : vdef list
    ; kvars  : kdef list
    ; cstrs  : cstr list 
    ; consts : vdef list
  }

type kmap 
  = kdef SM.t

(*************************************************************************)
(************* Rendering SMTLIB to String ********************************)
(*************************************************************************)

(* Printing as C syntax *)

let print_brel ppf = function
  | A.Eq -> F.fprintf ppf "="
  | A.Ne -> F.fprintf ppf "!="
  | A.Gt -> F.fprintf ppf ">"
  | A.Ge -> F.fprintf ppf ">="
  | A.Lt -> F.fprintf ppf "<"
  | A.Le -> F.fprintf ppf "<="

let print_bop ppf = function
  | A.Plus  -> F.fprintf ppf "+"
  | A.Minus -> F.fprintf ppf "-"
  | A.Times -> F.fprintf ppf "*"
  | A.Div   -> F.fprintf ppf "/"
  | A.Mod   -> F.fprintf ppf "mod"

let rec print_pred ppf pred =
  match P.unwrap pred with
  | A.True ->
      F.fprintf ppf "true"
  | A.False ->
      F.fprintf ppf "false"
  | A.Atom (e1, A.Ne, e2) ->
      F.fprintf ppf "(not (= %a %a))" 
        print_expr e1 
        print_expr e2
  | A.Atom (e1, r, e2) ->
      F.fprintf ppf "(%a %a %a)" 
        print_brel r 
        print_expr e1 
        print_expr e2
  | A.And ps ->
      Misc.pprint_many_prefix "and" A.pTrue print_pred ppf ps
  | A.Or ps ->
      Misc.pprint_many_prefix "or" A.pFalse print_pred ppf ps
  | A.Not p ->
      F.fprintf ppf "(not %a)" print_pred p
  | A.Imp (p1, p2) ->
      F.fprintf ppf "(implies %a %a)" 
        print_pred p1 
        print_pred p2
  | A.Iff (p1, p2) ->
      print_pred ppf (A.pAnd [A.pImp (p1, p2); A.pImp (p2, p1)])
  | A.Bexp e ->
      print_expr ppf e
  | _ -> assertf "ERROR: ToSmtLib.print_pred %s" (P.to_string pred)
      
and print_expr ppf expr =
  match E.unwrap expr with
  | A.Con c ->
      F.fprintf ppf "%a" A.Constant.print c
  | A.Var v ->
      F.fprintf ppf "%a" Sy.print v
  | A.App (f, es) ->
      F.fprintf ppf "(%a %a)" 
        Sy.print f
        (Misc.pprint_many false " " print_expr) es
  | A.Bin (e1, op, e2) ->
      F.fprintf ppf "(%a %a %a)"
        print_bop  op
        print_expr e1
        print_expr e2
  | A.Ite (p, e1, e2) ->
      F.fprintf ppf "(ite %a %a %a)"
        print_pred p
        print_expr e1
        print_expr e2
  | A.Cst (e, _) ->
      F.fprintf ppf "%a" print_expr e
  | _ -> assertf "ERROR: ToSmtLib.print_expr %s" (E.to_string expr)

let rec print_sort ppf t = match So.func_of_t t with
  | Some (_, ts, t) -> 
      Format.fprintf ppf "%a %a"
        (Misc.pprint_many false " " print_sort) ts
        print_sort t
  | None 
  when So.is_bool t -> 
    Format.fprintf ppf "Bool"
  | _ -> 
    Format.fprintf ppf "Int"

(*
let print_ty_kind ppf t = match So.func_of_t t with
  | Some (_, ts, t) when So.is_bool t -> Format.fprintf ppf "pred"
  | _                                 -> Format.fprintf ppf "fun"
*)

let print_vdef ppf (x, t) = match So.func_of_t t with
  | Some (_, ts, t') when So.is_bool t' -> 
      Format.fprintf ppf ":extrapreds ((%a %a))" 
        Sy.print x 
        (Misc.pprint_many false " " print_sort) ts
  | _ ->
      Format.fprintf ppf ":extrafuns ((%a %a))" 
        Sy.print x 
        print_sort t

  (*
let print_vdef ppf (x, t) = 
  Format.fprintf ppf ":extra%as ((%a %a))"
    print_ty_kind t
    Sy.print x
    print_sort t
*)

let print_const ppf c = 
  Format.fprintf ppf "; constant \n%a\n" print_vdef c

let groupConsts cs = 
  cs |> Misc.kgroupby snd 
     |> Misc.map (Misc.app_snd (List.map fst))
     |> List.filter (snd <+> List.length <+> (>) 0)

let print_distinct ppf (t, cs) =
  Format.fprintf ppf 
    "; distinct constants of sort: %a\n(distinct %a)\n"   
     print_sort t
     (Misc.pprint_many false " " Sy.print) cs

let print_kdef ppf (kf, xts) = 
  Format.fprintf ppf ":extrapreds ((%a %a))"
    Sy.print kf
    (Misc.pprint_many false " " print_sort) (List.map snd xts)

let print_rhs ppf = function
  | None   -> Format.fprintf ppf "false"
  | Some p -> Format.fprintf ppf "%a" print_pred p

let print_cstr ppf c = 
  Format.fprintf ppf "\n; cid = %d\n:assumption\n(implies (%a) %a)\n"
    c.id print_pred c.lhs print_rhs c.rhs

let print ppf smt = 
  Format.fprintf ppf 
    "(benchmark unknown\n:status unsat\n:logic AUFLIA\n%a\n%a\n%a\n%a\n%a\n)"
    (Misc.pprint_many true "\n" print_vdef)     smt.vars
    (Misc.pprint_many true "\n" print_const)    smt.consts
    (Misc.pprint_many true "\n" print_kdef)     smt.kvars
    (Misc.pprint_many true "\n" print_distinct) (groupConsts smt.consts)
    (Misc.pprint_many true "\n" print_cstr)     smt.cstrs

(*************************************************************************)
(************* Helpers for extracting var-sort bindings ******************) 
(*************************************************************************)

let sort_compat x t t' =
  Ast.Sort.compat t t'
  >> (fun b -> if not b then 
               Printf.printf "WARNING: k-sort incompatible for %s" 
               (Sy.to_string x))

(* HACKY sort_compat because in the end everything is an Int *)
let sort_compat x t1 t2 = 
  not (So.is_bool t1) 
  && not (So.is_bool t2) 
  && (not (So.is_func t1) || (t1 = t2))
  && (not (So.is_func t2) || (t1 = t2))

let vdefs_of_env env r = 
  env |> C.bindings_of_env
      |> (++) [(C.vv_of_reft r, r)]
      |> List.map (Misc.app_snd C.sort_of_reft)
      (* |> List.filter (not <.> So.is_func <.> snd)  *)
      |> Misc.fsort fst

(*************************************************************************)
(************* Build VMap : gather all vars/sorts for regular vars *******) 
(*************************************************************************)


let update_vmap vm (x, t) =
  Misc.maybe_iter begin fun t' ->
    asserts (sort_compat x t t') "ERROR: v-sort incompatible %s" (Sy.to_string x)
  end (SM.maybe_find x vm);
  SM.add x t vm

let update_vmap_int vm (x, t) =
  SM.add x So.t_int vm

let add_c_var_to_vmap vm c =
  let vvl = C.vv_of_reft (C.lhs_of_t c) in
  let vvr = C.vv_of_reft (C.rhs_of_t c) in
  let _   = asserts (vvl = vvr) "Different VVs in Constr: %d" (C.id_of_t c) in
  vdefs_of_env (C.env_of_t c) (C.lhs_of_t c)
  |> List.fold_left update_vmap_int vm 
 
let add_wf_var_to_vmap vm w =
  vdefs_of_env (C.env_of_wf w) (C.reft_of_wf w)
  |> List.fold_left update_vmap_int vm 
  
(*************************************************************************)
(************ Build KMap: gather scopes for each kvar from wfs** *********)
(*************************************************************************)

let check_no_subs wid suks = 
  asserts 
    (List.for_all (fst <+> A.Subst.is_empty) suks) 
    "NonTriv Subst wid=%d" wid

let join vds vds' = 
  let xm  = SM.of_list vds  in
  List.filter begin fun (x, t) ->
    match SM.maybe_find x xm with
    | None    -> false
    | Some t' -> sort_compat x t t'  
  end vds'       

let update_kmap vdefs km k : kmap =
  match SM.maybe_find k km with
  | None            -> SM.add k (k, vdefs) km
  | Some (_,vdefs') -> SM.add k (k, join vdefs vdefs') km

let add_wf_to_kmap km wf =
  let vdefs = vdefs_of_env (C.env_of_wf wf) (C.reft_of_wf wf) 
              |> List.filter (snd <+> So.is_func <+> not)
  in
  C.reft_of_wf wf
  |> C.kvars_of_reft  
  >> check_no_subs (C.id_of_wf wf) 
  |> List.map snd
  |> List.fold_left (update_kmap vdefs) km

let make_kmap defs : kmap = 
  defs 
  |> Misc.map_partial (function Cg.Wfc x -> Some x | _ -> None)
  |> List.fold_left add_wf_to_kmap SM.empty

let mkFreshI, _   = Misc.mk_int_factory ()
let mkFresh cid x = 
  Sy.of_string (Format.sprintf "%s_smt_%d_%d" (Sy.to_string x) cid (mkFreshI ())) 
(*  >> (fun x' -> Format.printf "fresh_var: %a \n" Sy.print x')
 *)

let fresh_vars env cid es = 
  let t   = Hashtbl.create 17 in
  let msg = "fresh_vars: cid = "^(string_of_int cid) in   
  let es' = List.map begin fun e -> match e with
            | (A.Var x, _) ->
                if Hashtbl.mem t x then
                  x |> mkFresh cid >> Hashtbl.add t x |> A.eVar
                else let _ = Hashtbl.add t x x in e 
            | _ -> failwith ("ERROR: " ^ msg)
            end es in
  let l' = Misc.hashtbl_keys t 
           |> Misc.flap begin fun x -> 
                let so = SM.safeFind x env msg in
                foreach (Hashtbl.find_all t x) begin fun x' ->
                  (x', so), A.pEqual ((A.eVar x), (A.eVar x'))
                end
              end
           |> List.split
           |> Misc.app_snd A.pAnd in
  l', es'

(*************************************************************************)
(************* Translating using the KMap ********************************)
(*************************************************************************)

let pred_of_kdef (kf, xts) =
  A.pBexp <| A.eApp (kf, List.map (fst <+> A.eVar) xts)  

let soln_of_kmap km k =
  [pred_of_kdef <| SM.safeFind k km "soln_of_kmap"]
  (* >> (Format.printf "soln_of_kmap: k = %a ps = %a \n" Sy.print k (Misc.pprint_many false " " P.print))
   *)

let tx_constraint s c =
  let cid     = C.id_of_t c                 in
  let lps     = C.preds_of_lhs_nofilter s c in
  let v,t,ras = C.rhs_of_t c                in
  ras |>: begin function 
            | C.Conc p -> { lhs = A.pAnd ((A.pNot p) :: lps)
                          ; rhs = None 
                          ; id = cid }
            | ra       -> { lhs = A.pAnd lps
                          ; rhs = (match C.preds_of_refa s ra with 
                                  | [p] -> Some p 
                                  | _   -> failwith "tx_constraint")
                          ; id = cid}
          end
       
       |>: begin function
         (* Ken needed this tx but it messes up with typeclasses... maybe not
          * needed any more?  
            
         | { rhs = Some (A.Bexp (A.App (f, es),_), _) } as c' ->
                let (xts, eqp), es' = fresh_vars (C.senv_of_t c) cid es in
                let r'              = A.pBexp (A.eApp (f, es')) in 
                (xts, {c' with lhs = A.pAnd [eqp; c'.lhs]; rhs = Some r' })
          *)
          |  c' -> ([], c')
          end

let tx_defs cfg =
  let defs = List.map (fun c -> Cg.Cst c) cfg.Cg.cs ++ 
             List.map (fun c -> Cg.Wfc c) cfg.Cg.ws     in
  let km   = defs |> make_kmap                          in
  let s    = soln_of_kmap km                            in 
  let cs   = cfg.Cg.cs                                  in
  let ws   = cfg.Cg.ws                                  in
  let xts,cs' = List.split <| Misc.flap (tx_constraint s) cs in
  { vars   =  Misc.flatten xts 
           ++ (SM.to_list <| List.fold_left add_c_var_to_vmap SM.empty cs) 
           ++ (SM.to_list <| List.fold_left add_wf_var_to_vmap SM.empty ws)
  ; kvars  = SM.range km
  ; cstrs  = cs'
  ; consts = SM.to_list cfg.Cg.uops 
  }


(*************************************************************************)
(************* API *******************************************************)
(*************************************************************************)

  (*
let render ppf cfg =
  cfg |> tx_defs 
      |> F.fprintf ppf "%a" print
*)
let dump_smtlib cfg =
  let _  = print_now ("BEGIN: Dump SMTLIB \n") in
  let me = tx_defs cfg                         in
  let _  = Misc.with_out_formatter !Constants.out_file (fun ppf -> F.fprintf ppf "%a" print me) in
  let _  = print_now ("DONE: Dump SMTLIB to " ^ !Constants.out_file ^"\n") in
  exit 1 


