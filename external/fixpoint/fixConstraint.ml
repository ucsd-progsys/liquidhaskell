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
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONSy.
 *
 *)

(* This module implements basic datatypes and operations on constraints *)
module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate
module Sy = A.Symbol
module So = A.Sort
module SM = Sy.SMap
module BS = BNstats
module Su = Ast.Subst
module Co  = Constants
module Misc = FixMisc 
module MSM = Misc.StringMap
open Misc.Ops

type tag  = int list * string
type id   = int
type dep  = Adp of tag * tag | Ddp of tag * tag | Ddp_s of tag | Ddp_t of tag

type refa = Conc of A.pred | Kvar of Su.t * Sy.t
type reft = Sy.t * A.Sort.t * refa list                (* { VV: t | [ra] } *)
type envt = reft SM.t
type wf   = envt * reft * (id option) * (Qualifier.t -> bool)
type t    = { full    : envt; 
              nontriv : envt;
              guard   : A.pred;
              iguard  : A.pred;
              lhs     : reft;
              rhs     : reft;
              ido     : id option;
              tag     : tag; }

type soln = Ast.Symbol.t -> Ast.pred list

exception BadConstraint of (id * tag * string)




(*
type soln    = Ast.pred list Ast.Symbol.SMap.t
type soln = { read  : Ast.Symbol.t -> Ast.pred list
            ; kvars : Ast.Symbol.SSet.t }
*)

let mydebug = false 

(*************************************************************)
(************************** Misc.  ***************************)
(*************************************************************)

let is_simple_refatom = function 
  | Kvar (s, _) -> Ast.Subst.is_empty s 
  | _           -> false

let is_tauto_refatom  = function 
  | Conc p -> P.is_tauto p 
  |  _ -> false
  

(* API *)
let fresh_kvar = 
  let tick, _  = Misc.mk_int_factory () in
  tick <+> string_of_int <+> (^) "k_" <+> Sy.of_string

(* API *)
let kvars_of_reft (_, _, rs) =
  Misc.map_partial begin function 
    | Kvar (subs, k) -> Some (subs,k) 
    | _              -> None 
  end rs

let meet x (v1, t1, ra1s) (v2, t2, ra2s) = 
  asserts (v1=v2 && t1=t2) "ERROR: FixConstraint.meet x=%s (v1=%s, t1=%s) (v2=%s, t2=%s)" 
  (Sy.to_string x) (Sy.to_string v1) (A.Sort.to_string t1) (Sy.to_string v2) (A.Sort.to_string t2) ;
  (v1, t1, Misc.sort_and_compact (ra1s ++ ra2s))

let env_of_bindings_ meetb xrs =
  List.fold_left begin fun env (x, r) -> 
    let r = if meetb && SM.mem x env then meet x r (SM.find x env) else r in
    SM.add x r env
  end SM.empty xrs

(* API *)
let env_of_bindings         = env_of_bindings_ true
let env_of_ordered_bindings = env_of_bindings_ false 

(* 
let env_of_bindings xrs =
  List.fold_left begin fun env (x, r) -> 
    let r = if SM.mem x env then meet x r (SM.find x env) else r in
    SM.add x r env
  end SM.empty xrs
*)

let bindings_of_env = SM.to_list

(* let bindings_of_env env = 
  SM.fold (fun x y bs -> (x,y)::bs) env []
*)

let split_ras ras = 
  let cras, kras = List.partition (function (Conc _) -> true | _ -> false) ras in
  cras |> Misc.map_partial (function Conc p -> Some p | _ -> None) 
       |> (function [] -> (None, kras) | ps -> (Some (A.pAnd ps), kras))


let kbindings_of_lhs {nontriv = ne; lhs = (v, t, ras)} =  
  let xkss     = SM.to_list ne in
  let _, kras  = split_ras ras in
  (v, (v,t,kras)) :: xkss

let map_env    = SM.mapi
let lookup_env = Misc.flip SM.maybe_find 
(* let lookup_env env x = try Some (SM.find x env) with Not_found -> None *)



(* API *)
let is_simple {lhs = (_,_,ra1s); rhs = (_,_,ra2s)} = 
  List.for_all is_simple_refatom ra1s 
  && List.for_all is_simple_refatom ra2s 
  && !Co.simple

let is_conc_refa = function Conc p -> not (P.is_tauto p) | _ -> false

(* API *)
let is_conc_rhs {rhs = (_,_,ras)} =
  List.exists is_conc_refa ras
  >> (fun rv -> if rv then (asserts (List.for_all is_conc_refa ras) "is_conc_rhs"))


(* API *)
let kvars_of_t {nontriv = env; lhs = lhs; rhs = rhs} =
  [lhs; rhs] 
  |> SM.fold (fun _ r acc -> r :: acc) env
  |> Misc.flap kvars_of_reft 




(*************************************************************)
(*********************** Logic Embedding *********************)
(*************************************************************)

let canon_ras ras = 
  match split_ras ras with
  | None, kras   -> kras
  | Some p, kras -> Conc p :: kras

(* 
let non_trivial env = 
  SM.fold begin fun x r sm -> match thd3 r with 
        | [] -> sm 
        | _::_ -> SM.add x r sm
  end env SM.empty
*)

let non_trivial env = 
  SM.fold begin fun x (v,t,ras) ((ne, ps) as acc) -> match ras with
    | [] -> acc 
    | _  -> let po, kras = split_ras ras in 
            let ne' = match kras with [] -> ne | _      -> SM.add x (v,t,kras) ne in
            let ps' = match po with None -> ps | Some p -> (P.subst p v (A.eVar x)) :: ps  in
            ne', ps'
  end env (SM.empty, []) 

(* API *)
let is_conc_refa = function
  | Conc _ -> true
  | _      -> false

let soln_read s k = s k (* SM.find k s *)

(* API *)
let preds_of_refa s = function
  | Conc p      -> [p]
  | Kvar (su,k) -> soln_read s k |> List.map (Misc.flip A.substs_pred su)

(* API *)
let preds_of_reft f (_,_,ras) = 
  Misc.flap (preds_of_refa f) ras

(* API *)
let meet_solution s1 s2 = fun k -> s1 k ++ s2 k (* SM.extendWith (fun _ -> (++)) *)
let empty_solution      = fun _ -> []

let apply_solution_refa f ra = 
  Conc (A.pAnd (preds_of_refa f ra))

(* API *)
let apply_solution f (v, t, ras) = 
  (v, t, List.map (apply_solution_refa f) ras)

let preds_of_envt f env =
  SM.fold
    (fun x ((vv, t, ras) as r) ps -> 
      let vps = preds_of_reft f r in
      let xps = List.map (fun p -> P.subst p vv (A.eVar x)) vps in
      xps ++ ps)
    env [] 

(* API *)
let wellformed_pred env = 
  A.sortcheck_pred (Misc.maybe_map snd3 <.> Misc.flip SM.maybe_find env)

(* API *)
let preds_of_lhs_nofilter f c = 
  let envps = preds_of_envt f c.nontriv in
  let r1ps  = preds_of_reft f c.lhs in
  (c.iguard :: envps) ++ r1ps


(* let preds_of_lhs f c =
  let env   = SM.add (fst3 c.lhs) c.lhs c.full in
  let wfp p = wellformed_pred env p 
              >> (fun b -> if not b then F.eprintf "WARNING: Malformed Lhs Pred (%a)\n" P.print p) in
  let ps    = preds_of_lhs_nofilter f c        in
  let ps'   = List.filter wfp ps               in
  if !Co.strictsortcheck && List.length ps != List.length ps' 
  then raise (BadConstraint (Misc.maybe c.ido, c.tag, "Malformed Lhs Pred"))
  else ps
*)

let report_wellformed env c p wf = 
  if not wf then
    let msg = F.sprintf "WARNING: Malformed Lhs Pred (%s)\n" (P.to_string p)                  in 
    let _   = F.eprintf "%s" msg                                                              in 
    let _   = SM.iter (fun s (_,t,_) -> F.eprintf "@[%a :: %a@]@." Sy.print s So.print t) env in
    let _   = F.eprintf "@[%a@]@.@." P.print p                                                in
    if !Co.strictsortcheck then raise (BadConstraint (Misc.maybe c.ido, c.tag, msg))

(* API *)
let preds_of_lhs f c = 
  let env = SM.add (fst3 c.lhs) c.lhs c.full in
  preds_of_lhs_nofilter f c 
  |> List.filter (fun p -> wellformed_pred env p >> report_wellformed env c p)

(* API *)
let vars_of_t f ({rhs = r2} as c) =
  (preds_of_reft f r2) ++ (preds_of_lhs f c)
  |> Misc.flap P.support

(**************************************************************)
(********************** Pretty Printing ***********************)
(**************************************************************)

let print_refineatom ppf = function
  | Conc p       -> F.fprintf ppf "%a" P.print p
  | Kvar (su, k) -> F.fprintf ppf "%a%a" Sy.print k Su.print su

(*
(* API *)
let print_ras so ppf = function 
  | []  -> F.fprintf ppf "true"
  | ras -> begin match so with 
            | None   ->
               F.fprintf ppf "%a" (Misc.pprint_many_box false "" "; " "" print_refineatom) ras 
             | Some s -> let ps = Misc.flap (preds_of_refa s) ras in
                         (match ps with 
                         | [] -> F.fprintf ppf "[]" 
                         | _  -> F.fprintf ppf "%a" P.print (A.pAnd ps))
           end
*)

(* API *)
let print_ras so ppf ras = match so with
  | None  -> 
      Misc.pprint_many_box false "[" "; " "]" print_refineatom ppf ras
  | Some s -> 
      begin match Misc.flap (preds_of_refa s) ras with 
            | [] -> F.fprintf ppf "[]"
            | ps -> F.fprintf ppf "[%a]" P.print (A.pAnd ps)
      end


(* API *)
let print_reft_pred so ppf (v,t,ras) =
  F.fprintf ppf "@[{%a:%a | %a}@]"
    Sy.print v 
    Ast.Sort.print t
    (print_ras so) ras

(*
let print_reft_pred so ppf = function
  | (v,_,[])  -> F.fprintf ppf "@[{%a | true }@]" Sy.print v
  | (v,_,ras) -> F.fprintf ppf "@[{%a | @[%a@]}@]" Sy.print v (print_ras so) ras
*)

(* API *)
let print_reft so ppf (v, t, ras) =
  F.fprintf ppf "@[{%a : %a | %a}@]" 
    Sy.print v 
    Ast.Sort.print t
    (print_ras so) ras

(* API *)
let print_binding so ppf (x, r) = 
  F.fprintf ppf "@[%a:%a@]" Sy.print x (print_reft so) r 

(* API *)
let print_env so ppf env = 
  bindings_of_env env 
  |> F.fprintf ppf "@[%a@]" (Misc.pprint_many_brackets true (print_binding so))


let pprint_id ppf = function
  | Some id     -> F.fprintf ppf "id %d" id
  | None        -> F.fprintf ppf ""


let string_of_intlist = (String.concat ";") <.> (List.map string_of_int)

(* API *)
let print_tag ppf = function
  | [],_ -> F.fprintf ppf ""
  | is,s -> F.fprintf ppf "tag [%s] //%s" (string_of_intlist is) s 

(* API *)
let print_dep ppf = function
  | Adp ((t,_), (t',_)) 
    -> F.fprintf ppf "add_dep: [%s] => [%s]" (string_of_intlist t) (string_of_intlist t')
  | Ddp ((t,_), (t',_)) 
    -> F.fprintf ppf "del_dep: [%s] => [%s]" (string_of_intlist t) (string_of_intlist t')
  | Ddp_s (t,_)    
    -> F.fprintf ppf "del_dep: [%s] => *" (string_of_intlist t) 
  | Ddp_t (t',_)    
    -> F.fprintf ppf "del_dep: * => [%s]" (string_of_intlist t')

(* API *)
let print_wf so ppf (env, r, io, _) =
  F.fprintf ppf "wf: env @[%a@] @\n reft %a @\n %a @\n"
    (print_env so) env
    (print_reft so) r
    pprint_id io

let print_t so ppf c =
  let env, g = if !Co.print_nontriv then c.nontriv, c.iguard else c.full, c.guard in 
  F.fprintf ppf 
  "constraint:@. env  @[%a@] @\n grd @[%a@] @\n lhs @[%a@] @\n rhs @[%a@] @\n %a %a @\n"
    (print_env so) env 
    P.print g
    (print_reft so) c.lhs 
    (print_reft so) c.rhs
    pprint_id c.ido
    print_tag c.tag 

(* API *)
let to_string         = Misc.fsprintf (print_t None)
let refa_to_string    = Misc.fsprintf print_refineatom 
let reft_to_string    = Misc.fsprintf (print_reft None)
let binding_to_string = Misc.fsprintf (print_binding None) 


 
(***************************************************************)
(*********************** Getter/Setter *************************)
(***************************************************************)

let theta_ra (su': Su.t) = function
  | Conc p       -> Conc (A.substs_pred p su')
  | Kvar (su, k) -> Kvar (Su.compose su su', k) 


(* API *)
let make_reft     = fun v so ras -> (v, so, List.map (theta_ra Su.empty) (canon_ras ras))

let vv_of_reft    = fst3
let sort_of_reft  = snd3
let ras_of_reft   = thd3
let shape_of_reft = fun (v, so, _) -> (v, so, [])
let theta         = fun subs (v, so, ras) -> (v, so, Misc.map (theta_ra subs) ras)


(* API *)
let env_of_t    = fun t -> t.full 
let grd_of_t    = fun t -> t.guard 
let lhs_of_t    = fun t -> t.lhs 
let rhs_of_t    = fun t -> t.rhs
let tag_of_t    = fun t -> t.tag
let ido_of_t    = fun t -> t.ido
let id_of_t     = fun t -> match t.ido with Some i -> i | _ -> assertf "C.id_of_t"
let is_tauto    = rhs_of_t <+> ras_of_reft <+> List.for_all is_tauto_refatom
let make_t      = fun env p r1 r2 io is ->
                    let p        = A.simplify_pred p in
                    let ne, ps   = non_trivial env   in
                    { full    = env 
                    ; nontriv = ne
                    ; guard   = p
                    ; iguard  = A.pAnd (p::ps) 
                    ; lhs     = r1 
                    ; rhs     = r2
                    ; ido     = io
                    ; tag     = is }

let vv_of_t     = fun t -> fst3 t.lhs
let sort_of_t   = fun t -> snd3 t.lhs
let senv_of_t   = fun t -> SM.map snd3 t.full
                        |> SM.add (vv_of_t t) (sort_of_t t) 

(*
let make_t      = fun env p ((v,t,ras1) as r1) r2 io is ->
                    let p        = A.simplify_pred p in
                    let po, kras = split_ras ras1    in
                    let ne, ps   = non_trivial env   in
                    let gps      = match po with Some p' -> p' :: p :: ps | _ -> p :: ps in
                    { full    = env 
                    ; nontriv = ne
                    ; guard   = p
                    ; iguard  = A.pAnd gps 
                    ; lhs     = (v, t, kras) 
                    ; rhs     = r2
                    ; ido     = io
                    ; tag     = is }
*)

let reft_of_sort so = make_reft (Sy.value_variable so) so []

let add_consts_env consts env =
  consts
  |> List.map (Misc.app_snd reft_of_sort)
  |> List.fold_left (fun env (x,r) -> SM.add x r env) env

(* API *)
let add_consts_wf consts (env,x,y,z) = (add_consts_env consts env, x, y, z)

(* API *)
let add_consts_t consts t = {t with full = add_consts_env consts t.full}

(* API *)
let make_wf          = fun env r io -> (env, r, io, fun _ -> true)
let make_filtered_wf = fun env r io fltr -> (env, r, io, fltr)
let env_of_wf        = fst4
let reft_of_wf       = snd4
let id_of_wf         = function (_,_,Some i,_) -> i | _ -> assertf "C.id_of_wf"
let filter_of_wf     = fth4
  
let intersect_maps m1 m2 = SM.filter begin fun k elt ->
  SM.mem k m2 && SM.find k m2 = elt
end m1
  
let intersect_wfs (e1, r1, id1, qf1) (e2, r2, id2, qf2) =
  let _ = assert (r1 = r2) in
  let env = intersect_maps e1 e2 in
  (env, r1, id1, fun x -> (qf1 x && qf2 x))
    
let reduce_wfs wfs = 
  wfs 
  |> Misc.groupby reft_of_wf 
  |>: (fun wfs -> List.fold_left intersect_wfs (List.hd wfs) (List.tl wfs))


(* API *)
let matches_deps ds = 
  let tt   = H.create 37 in
  let s_tt = H.create 37 in
  let t_tt = H.create 37 in
  List.iter begin function  
    | Adp (t, t') 
    | Ddp (t, t') -> H.add tt (t,t') ()
    | Ddp_s t     -> H.add s_tt t  ()
    | Ddp_t t'    -> H.add t_tt t' ()
  end ds;
  (fun (t, t') -> H.mem tt (t, t') || H.mem s_tt t || H.mem t_tt t')

(* API *)
let pol_of_dep = function Adp (_,_) -> true | _ -> false

(* API *)
let tags_of_dep = function 
  | Adp (t, t') | Ddp (t, t') -> t,t' 
  | _ -> assertf "tags_of_dep"

(* API *)
let make_dep b xo yo =
  match (b, xo, yo) with
  | true , Some t, Some t' -> Adp (t, t')
  | false, Some t, Some t' -> Ddp (t, t')
  | false, Some t, None    -> Ddp_s t
  | false, None  , Some t' -> Ddp_t t'
  | _                      -> assertf "FixConstraint.make_dep: match failure"

(* API *)
let preds_kvars_of_reft reft =
  List.fold_left begin fun (ps, ks) -> function 
    | Conc p -> p :: ps, ks
    | Kvar (xes, kvar) -> ps, (xes, kvar) :: ks 
  end ([], []) (ras_of_reft reft)


(***************************************************************)
(************* Add Distinct Ids to Constraints *****************)
(***************************************************************)

let max_id n cs =
  cs |> Misc.map_partial ido_of_t 
     >> (fun ids -> asserts (Misc.distinct ids) "Duplicate Ids")
     |> List.fold_left max n

let max_wf_id n ws =
  ws |> Misc.map_partial (fun (_,_,ido,_) -> ido) 
     >> (fun ids -> asserts (Misc.distinct ids) "Duplicate WF Ids")
     |> List.fold_left max n

(* API *)
let add_wf_ids ws = 
  Misc.mapfold begin fun j wf -> match wf with
    | (x,y,None,z) -> j+1, (x, y, Some j, z) 
    | _            -> j, wf
  end ((max_wf_id 0 ws) + 1) ws
  |> snd
    
(* API *)
let add_ids n cs =
  Misc.mapfold begin fun j c -> match c with
    | {ido = None} -> j+1, {c with ido = Some j}
    | c            -> j, c
  end ((max_id n cs) + 1) cs
