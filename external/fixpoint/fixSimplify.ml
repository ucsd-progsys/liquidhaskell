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
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *)

module BS = BNstats
module Co = Constants
module C  = FixConstraint
module P  = Ast.Predicate
module E  = Ast.Expression
module Sy = Ast.Symbol
module Kg = Kvgraph
module Su = Ast.Subst
module SM = Ast.Symbol.SMap
module SS = Ast.Symbol.SSet

module Misc = FixMisc 
module IM = Misc.IntMap
open Misc.Ops
open Ast

let mydebug = false


(****************************************************************************)
(*********************************** Misc. **********************************)
(****************************************************************************)

let add_cm     = List.fold_left (fun cm c -> IM.add (C.id_of_t c) c cm) 
let find_cm    = fun cm id -> IM.find id cm
let refas_of_k = fun k -> [C.Kvar (Su.empty, k)] 

(****************************************************************************)
(************** Generic Simplification/Transformation API *******************)
(****************************************************************************)

module type SIMPLIFIER = sig
  val simplify_ts: FixConstraint.t list -> FixConstraint.t list
end

(****************************************************************************)
(******************* Syntactic Simplification *******************************)
(****************************************************************************)

module Syntactic : SIMPLIFIER = struct

let defs_of_pred = 
  let rec dofp (em, pm) p = match p with
    | Atom ((Var v, _), Eq, e), _ 
      when not (P.is_tauto p) -> 
        Sy.SMap.add v e em, pm
    | And [Imp ((Bexp (Var v1, _), _), p1), _; 
           Imp (p2, (Bexp (Var v2, _), _)), _], _ 
      when v1 = v2 && p1 = p2 && not(P.is_tauto p) -> 
        em, Sy.SMap.add v1 p1 pm
    | And ps, _ -> 
        List.fold_left dofp (em, pm) ps
    | _ -> em, pm
  in dofp (Sy.SMap.empty, Sy.SMap.empty)

let rec expr_apply_defs em pm expr = 
  let ef = expr_apply_defs em pm in
  let pf = pred_apply_defs em pm in
  match expr with 
  | Var v, _ when Sy.SMap.mem v em ->
      Sy.SMap.find v em, true
  | Var _, _ | Con _, _ | Bot, _ ->
      expr, false
  | App (v, es), _ -> 
      let _  = asserts (not (Sy.SMap.mem v em)) "binding for UF" in
      es |> List.map ef 
         |> List.split 
         |> (fun (es', bs') -> (eApp (v, es'), List.fold_left (||) false bs'))
  | Bin (e1, op, e2), _ -> 
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      eBin (e1', op, e2'), (b1' || b2')
  | Ite (p, e1, e2), _ -> 
      let p', b'   = pf p in
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      eIte (p', e1', e2'), (b' || b1' || b2')
  | Fld (v, e), _ -> 
      let e', b'   = ef e in
      eFld (v, e'), b'
  | Cst (e, t), _ ->
      let e', b'   = ef e in
      eCst (e', t), b'
  | _ -> failwith "Pattern: expr_apply_defs"

and pred_apply_defs em pm pred =
  let ef = expr_apply_defs em pm in
  let pf = pred_apply_defs em pm in
  match pred with 
  | And ps, _ -> 
      ps |> List.map pf
         |> List.split
         |> (fun (ps', bs') -> pAnd ps', List.exists id bs') 
  | Or ps, _ -> 
      ps |> List.map pf
         |> List.split
         |> (fun (ps', bs') -> pOr ps', List.exists id bs') 
  | Not p, _ ->
       p |> pf 
         |> Misc.app_fst pNot
  | Imp (p1, p2), _ -> 
      let p1', b1' = pf p1 in
      let p2', b2' = pf p2 in
      pImp (p1', p2'), b1' || b2'
  | Bexp (Var v, _), _ when Sy.SMap.mem v pm ->
      Sy.SMap.find v pm, true
  | Bexp e, _ ->
      e |> ef |> Misc.app_fst pBexp
  | Atom (e1, brel, e2), _ ->
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      pAtom (e1', brel, e2'), b1' || b2'
  | Forall (qs, p), _ -> 
      assertf "Forall in Simplify!"
  | _ ->
      pred, false

(* Why does this fixpointing terminate?
 * close em, pm under substitution so that
   for all x in dom(em), support(em(x)) \cap dom(em) = empty *)

(* Assume: em is well-formed, 
 * i.e. exists an ordering on vars of dom(em)
 * x1 < x2 < ... < xn s.t. if xj \in em(xi) then xj < xi *)

let expr_apply_defs em fm e = 
  e |> Misc.fixpoint (expr_apply_defs em fm) 
    |> fst

let pred_apply_defs em fm p = 
  p |> Misc.fixpoint (pred_apply_defs em fm) 
    |> fst
    |> simplify_pred

let subs_apply_defs em pm xes = List.map (Misc.app_snd (expr_apply_defs em pm)) xes


let print_em_pm t (em, pm) =
  let id   = t |> C.id_of_t in
  let vv   = t |> C.lhs_of_t |> C.vv_of_reft in
  let vve  = try Sy.SMap.find vv em with Not_found -> bot in
  let vve' = expr_apply_defs em pm vve in
  Co.bprintf mydebug "\nbodyp em map for %d\n" id ;
  Sy.SMap.iter (fun x e -> Co.bprintf mydebug "%a -> %a\n" Sy.print x  E.print e) em;
  Co.bprintf mydebug "\nbodyp pm map for %d\n" id ;
  Sy.SMap.iter (fun x p -> Co.bprintf mydebug "%a -> %a\n" Sy.print x  P.print p) pm;
  Co.bprintf mydebug "edef for vv %a = %a (simplified %a)\n" Sy.print vv E.print vve E.print vve'

let preds_kvars_of_env env =
  Sy.SMap.fold begin fun x r (ps, env) -> 
    let vv       = C.vv_of_reft r in
    let xe       = Ast.eVar x in
    let t        = C.sort_of_reft r in
    let rps, rks = C.preds_kvars_of_reft r in
    let ps'      = List.map (fun p -> P.subst p vv xe) rps ++ ps in
    let env'     = (* match rks with [] -> env | _ -> *) Sy.SMap.add x (vv, t, rks) env in
    ps', env'
  end env ([], Sy.SMap.empty)

let simplify_kvar em pm (su, sym) =
  su |> Su.to_list 
     |> subs_apply_defs em pm
     |> Su.of_list
     |> (fun su -> C.Kvar (su, sym))

let simplify_env em pm ks_env = 
  Sy.SMap.map begin fun (vv, t, ks) -> 
    ks |> List.map (simplify_kvar em pm) |> C.make_reft vv t
  end ks_env

let simplify_grd em pm vv t p =
  let _  = Co.bprintf mydebug "simplify_grd [1]: %a \n" P.print p in
  let p  = pred_apply_defs em pm p in
  let _  = Co.bprintf mydebug "simplify_grd [2]: %a \n" P.print p in
  begin try 
    Sy.SMap.find vv em 
    |> expr_apply_defs em pm
    |> (fun vve -> pAnd [p; pAtom (eVar vv, Eq, vve)])
  with Not_found -> p end
  >> Co.bprintf mydebug "simplify_grd [3]: %a \n" P.print

let simplify_refa em pm = function 
  | C.Conc p          -> C.Conc (pred_apply_defs em pm p) 
  | C.Kvar (xes, sym) -> simplify_kvar em pm (xes, sym)

(* API *)
let simplify_t c = 
  let id             = c |> C.id_of_t in
  let _              = Co.bprintf mydebug "============== Simplifying %d ============== \n"id in
  let env_ps, ks_env = c |> C.env_of_t |> preds_kvars_of_env in
  let l_ps, l_ks     = c |> C.lhs_of_t |> C.preds_kvars_of_reft in
  let vv, t          = c |> C.lhs_of_t |> Misc.tmap2 (C.vv_of_reft, C.sort_of_reft) in
  let bodyp          = Ast.pAnd ([C.grd_of_t c] ++ l_ps ++ env_ps) 
                       >> Co.bprintf mydebug "body_pred: %a \n" P.print in
  let em, pm         = defs_of_pred bodyp                          
                       >> print_em_pm c in

  let senv           = simplify_env em pm ks_env in
  let sgrd           = simplify_grd em pm vv t bodyp in
  let slhs           = l_ks |> List.map (simplify_kvar em pm) |> C.make_reft vv t in
  let srhs           = c |> C.rhs_of_t |> C.ras_of_reft |> List.map (simplify_refa em pm) |> C.make_reft vv t in
  
  C.make_t senv sgrd slhs srhs (C.ido_of_t c) (C.tag_of_t c)

(* API *)
let simplify_ts cs = 
  cs |> List.map simplify_t
    (* |> List.filter (not <.> C.is_tauto) *) 
end

(****************************************************************************)
(*** Cone-of-Influence: Remove Constraints that don't reach constant-pred ***)
(****************************************************************************)

module Cone : SIMPLIFIER = struct
  let simplify_ts cs =
    let cm = add_cm IM.empty cs in 
    cs |> Kg.add Kg.empty 
       >> Kg.print_stats
       |> Kg.cone_ids 
       |> List.map (find_cm cm)
end

(**************************************************************************)
(*** Direct-Dependencies: Remove non-data-dependent binders****************)
(*************************************************************************)

module WeakFixpoint : SIMPLIFIER = struct
 
  let weaken_env c e = 
    C.make_t e 
      (C.grd_of_t c) (C.lhs_of_t c) (C.rhs_of_t c) 
      (C.ido_of_t c) (C.tag_of_t c)

  let support_of_refa = function 
    | C.Conc p -> P.support p
    | _        -> []

  let support_of_reft = 
    Misc.flap support_of_refa <.> thd3

  let rec data_cone env m n xs = match xs with 
    | _::_ -> let m' = List.fold_left (fun m' x -> Sy.SMap.add x n m') m xs in
              xs |> Misc.map_partial (C.lookup_env env) 
                 |> Misc.flap support_of_reft
                 |> Misc.filter (fun x -> not (Sy.SMap.mem x m))
                 |> data_cone env m' (n+1)
    | []   -> m
  
  let data_cone c = 
    (P.support (C.grd_of_t c)) 
    |> (++) (support_of_reft (C.lhs_of_t c))
    |> data_cone (C.env_of_t c) Sy.SMap.empty 0

  let project_cone m x ((v,t,ras) as r) =
    if Sy.SMap.mem x m then r else (v, t, List.filter C.is_conc_refa ras)

  let simplify_t c =
    c |> data_cone |> project_cone |> C.map_env 
      |> (fun f -> f (C.env_of_t c))
      |> weaken_env c
      
  let simplify_ts = Misc.map simplify_t
end

(****************************************************************************)
(***** Merge Write and Read of Kvar: A |- k and B, k |- C  iff A,B |- C  ****)
(****************************************************************************)

module EliminateK : SIMPLIFIER = struct
  
  type t = { g  : Kg.t;
             cm : FixConstraint.t IM.t;
             id : int; }

  let print_k ppf k = 
    Format.fprintf ppf "%s" (C.refa_to_string k)

  let empty  = 
    { g  = Kg.empty; 
      cm = IM.empty; 
      id = 0; }
 
  let add me cs = 
    let n, cs = C.add_ids me.id cs in 
    { g  = Kg.add me.g cs; 
      cm = add_cm me.cm cs; 
      id = n+1 }
 
  let remove me (k, cs) =
    { g  = Kg.remove me.g [k]; 
      cm = List.map C.id_of_t cs |> List.fold_left (Misc.flip IM.remove) me.cm;
      id = me.id; }
 
  let of_ts     = add empty 
  let to_ts     = fun me -> me.cm |> IM.to_list |> List.map snd
  let cs_of_k   = fun f me k ->  f me.g [k] |> List.map (find_cm me.cm)

  (* Assume that k is written in (1) and read once in (2)
     
     (1) env1, g1, k_v:l1                       |- k[xi := ai]
     (2) env2, g2, y:k[xi := bi]                |- r2
     
     Now, (1) equiv (1') and (2) equiv (2')
     
     (1') env1, g1, #i:{v=ai}, k_v:l1                           |- k[xi := #i]
     (2') env2, g2, #i:{v=bi}, y:k2[xi := #i]                   |- r2
     
     Next, we can merge (1') and (2')
     
     (1'+2') env1 ++ env2, g1 && g2, #i:{v=ai}, #i:{v=bi}, y:l1 |- r2
     
     Which simplifies to:
     
     (1'+2') env1 ++ env2, g1 && g2 && {ai = bi}, y:l1          |- r2
  *)

  let meet_env env1 env2 xrs =
    [env1; env2]
    |> Misc.flap C.bindings_of_env 
    |> (++) xrs 
    |> C.env_of_bindings

  let meet_sub su1 su2 =
    [su1; su2]
    |> Misc.flap Su.to_list
    |> Misc.groupby fst 
    |> List.map (function [(x,e)] -> pEqual (eVar x, e)| [(_,e1);(_,e2)] -> pEqual (e1,e2))
    |> pAnd

  let merge_one me k (wc, rc) =
    let env1, env2       = Misc.map_pair C.env_of_t (wc, rc) in 
    let g1, g2           = Misc.map_pair C.grd_of_t (wc, rc) in
    let l1               = C.lhs_of_t wc in
    let [C.Kvar(su1, k)] = C.rhs_of_t wc |> thd3 in
    let su2, yr', l'     = match Kg.k_reads me.g (C.id_of_t rc) (C.Kvar (Su.empty, k)) with 
                           | [Kg.Bnd (y, su2)] -> su2, [(y,l1)], (C.lhs_of_t rc)
                           | [Kg.Lhs su2]      -> su2, [], l1 
                           | _ -> assertf "EliminateK.merge_one (k=%s, id=%d)" (Sy.to_string k) (C.id_of_t rc) in
    let env'             = meet_env env1 env2 yr'          in
    let g'               = pAnd [g1; g2; meet_sub su1 su2] in
    let r'               = C.rhs_of_t rc                   in
    C.make_t env' g' l' r' None (C.tag_of_t rc)
    
  let eliminate me (k, wcs, rcs)  =
    me >> (fun _ -> Format.printf "EliminateK.eliminate %s \n" (C.refa_to_string k))  
       |> Misc.flip add    (Misc.cross_product wcs rcs |> List.map (merge_one me k)) 
       |> Misc.flip remove (k, wcs ++ rcs)

  let select_ks me = 
    me.g 
    |> Kg.filter_kvars (Kg.is_single_wr me.g) 
    |> List.filter (Kg.is_single_rd me.g)
    |> List.map (fun k -> (k, cs_of_k Kg.writes me k, cs_of_k Kg.reads me k))
    |> List.filter (fun (_,wcs, rcs) -> Misc.disjoint wcs rcs)
    >> (List.map fst3 <+> Format.printf "EliminateK.select_ks [OUT]: %a \n" 
                          (Misc.pprint_many false "," print_k))

  let simplify_ts cs =
    let me = of_ts cs in
    me |> select_ks
       |> List.fold_left eliminate me 
       |> to_ts 
end


(****************************************************************************)
(***** Copy Propagation *****************************************************)
(****************************************************************************)

module CopyProp : SIMPLIFIER = struct

  let subst_theta = 
    List.map <.> Misc.app_snd <.> (fun (x, e) e' -> E.subst e' x e) 
  
  let subst_bind su x y ((v, t, ras) as r) =  
    if x = y then (v, t, []) else C.theta su r

  let subst_cstr (x, e) c =
    let su    = Su.of_list [(x, e)]                         in
    let env'  = C.env_of_t c |> C.map_env (subst_bind su x) in
    let grd'  = C.grd_of_t c |> (fun p -> P.subst p x e)    in
    let lhs'  = C.lhs_of_t c |> C.theta su                  in
    let rhs'  = C.rhs_of_t c |> C.theta su                  in
    C.make_t env' grd' lhs' rhs' (C.ido_of_t c) (C.tag_of_t c)
  
  let rec eliminate c = function 
      | (x, e) :: theta' when List.mem x (E.support e)
        -> eliminate c theta'
      | xe :: theta' (* x not in e *)
        -> eliminate (subst_cstr xe c) (subst_theta xe theta') 
      | []  -> c
 
  let rigid_vars c =
    c |> C.kvars_of_t 
      |> List.map fst 
      |> Misc.flap Su.to_list 
      |> List.map fst 
      |> SS.of_list 

  let equalities_of_binding = function 
    | (x, (v, _, [C.Conc ( Atom ((Var v', _), Eq, e), _  )])) 
      when v = v' -> Some (x, e)
    | (x, (v, _, [C.Conc (  Atom (e, Eq, (Var v', _)), _ )])) 
      when v = v' -> Some (x, e)
    | _ -> None

  let equalities_of_t c =
    c |> C.env_of_t 
      |> (fun _ -> failwith "CopyProp.equalities_of_t") (* C.bindings_of_env  *)
      |> Misc.map_partial equalities_of_binding

  let simplify_t c = 
    let ys = rigid_vars c in
    c |> equalities_of_t 
      |> List.filter (fun (x,_) -> not (SS.mem x ys))
      |> eliminate c

  let simplify_ts = Misc.map simplify_t
end

(* API *)
let simplify_ts cs =
  cs 
  |> Misc.filter (not <.> C.is_tauto)
  |> ((not !Co.lfp)  <?> BS.time "simplify 0" WeakFixpoint.simplify_ts)
  |> BS.time "add ids  1" (C.add_ids 0) 
  |> snd
  (* |> (!Co.copyprop   <?> BS.time "simplify CP" CopyProp.simplify_ts)  *)
  |> (!Co.simplify_t <?> BS.time "simplify 1" Syntactic.simplify_ts) (* termination bug, tickled by C benchmarks *)
  |> (!Co.simplify_t <?> BS.time "simplify 2" Cone.simplify_ts)
  |> (!Co.simplify_t <?> BS.time "simplify 3" EliminateK.simplify_ts)
