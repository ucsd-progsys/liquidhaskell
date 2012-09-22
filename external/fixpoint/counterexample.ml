(*
 * Copyright © 2009-12 The Regents of the University of California. All rights reserved. 
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

(***************************************************************)
(* Counterexample Generation (cf. Lahiri-Vanegue, VMCAI 2011) **) 
(***************************************************************)

module F  = Format
module BS = BNstats
module C  = FixConstraint

module Misc = FixMisc 
module IM = Misc.IntMap
module IS = Misc.IntSet

module A  = Ast
module Sy = A.Symbol
module SM = Sy.SMap 
module SS = Sy.SSet
module P  = A.Predicate
module Su = A.Subst
module Q  = Qualifier
module TP  = TpNull.Prover

open Misc.Ops

let mydebug   = false

(***************************************************************************)
(************** Type Aliases ***********************************************)
(***************************************************************************)

type step  = int
type kvar  = Sy.t
type fact  = Abs of kvar * Qualifier.t | Conc of C.id
type cause = step * C.id * ((Sy.t * fact) list)

(* [k |-> [(i0, [q_i0_1...]),...]] 
 * where q_i0_1... are killed at timestep i0 for kvar k sorted by step *)
type lifespan = (step * Q.t list) list SM.t 

(* [id |-> i0,...] 
 * where the constraint id is selected at steps i0... by solver *)
type ctrace  = step list IM.t 

(* [((x1,k1,q1), c1);...;((xn,kn,qn),cn)] 
 * where each k_i+1, q_i+1, c_i+1 is the "cause" for why k_i, q_i is killed *)
(* type cex     = (Sy.t * fact * C.id) list *)
type cex     = Cause of Sy.t * fact * C.id * cex list

(****************************************************************************)
(******************** Printing Counterexamples ******************************)
(****************************************************************************)

let print_fact ppf = function
  | Abs (k, q) -> F.fprintf ppf "(%a/%a)" Sy.print k Q.print_args q
  | Conc i     -> F.fprintf ppf "(id %d)" i

let print_step ppf (x, f, cid) =
  F.fprintf ppf "%a: %a @@ %d" Sy.print x print_fact f cid

(*
let print_cex = Misc.pprint_many_box true "" "---> " "" print_step
*)

let rec print_cex spaces ppf (Cause (x, f, cid, cs)) =
  F.fprintf ppf "%s `-> %a\n%a" 
    (String.concat "" (Misc.clone " " spaces))
    print_step (x, f, cid) 
    (Misc.pprint_many false "\n\n" (print_cex (spaces + 4))) cs

let print_cex = print_cex 0

let print_fact_causes n ppf (f, xfs) =
  F.fprintf ppf "fact %a killed at %d by: %a \n"
    print_fact f
    n
    (Misc.pprint_many_brackets false  (Misc.pprint_tuple Sy.print print_fact)) xfs

(****************************************************************************)
(******************** Instance Type *****************************************)
(****************************************************************************)

let compare_fact f1 f2 =
  compare (Misc.fsprintf print_fact f1) (Misc.fsprintf print_fact f2)

module FactMap = Misc.EMap (struct 
  type t = fact
  let compare = compare_fact
  let print   = print_fact
end)

type t = { tpc      : TP.t 
         ; n        : int                   (* number of solver iters *)
         ; s        : FixConstraint.soln
         ; cm       : FixConstraint.t IM.t
         ; ctrace   : ctrace 
         ; lifespan : lifespan              (* builds soln at n                *)
         ; fsm      : step FactMap.t        (* fact |-> step at which killed   *)
         ; scm      : int IM.t              (* step |-> constr at step         *)
         }

let scm_of_ctrace ctrace = 
  ctrace 
  |> IM.to_list 
  |> Misc.flap (fun (cid, is) -> List.map (fun i -> (i, cid)) is)
  |> Misc.fsort fst
  |> IM.of_list

let fsm_of_lifespan lifetime =
  SM.fold begin fun k sqs fsm ->
    List.fold_left begin fun fsm (step, qs) -> 
      List.fold_left begin fun fsm q -> 
        FactMap.add (Abs (k, q)) step fsm
      end fsm qs
    end fsm sqs
  end lifetime FactMap.empty 

(************************************************************************)
(*********** Helpers to Reconstitute Solutions and Candidates ***********)
(************************************************************************)

let constrOfId me cid = 
   IM.safeFind cid me.cm "Cex.constrOfId"

let solutionAt me n k =
  SM.safeFind k me.lifespan "solutionAt: bad kvar"
  |> List.filter (fun (m,_) -> n <= m) 
  |> Misc.flap snd
  |> Misc.map Q.pred_of_t
  |> (++) (me.s k)

let isUnsatAt me c n = 
  let s     = solutionAt me n                                 in
  let rhsp  = A.pAnd <| C.preds_of_reft s (C.rhs_of_t c)      in
  let query = A.pAnd <| (A.pNot rhsp) :: (C.preds_of_lhs s c) in
  not <| TP.is_contra me.tpc (C.senv_of_t c) query

let prevStep_conc me c : int =
  let _  = asserts (C.is_conc_rhs c) in
  let no = Misc.find_first_true (isUnsatAt me c) 0 me.n in
  Misc.maybe_apply (+) no (-1)

let prevStep_abs me cid n : int = 
  let rec go n = function
    | m1 :: _ when m1 = n     -> (-1)
    | m1 :: (m2 :: _ as rest) -> if n = m2 then m1 else go n rest
    | _                       -> assertf "prevStep with bad ctrace"
  in go n (IM.safeFind cid me.ctrace "prevStep: bad cid") 

let prevStep me c n = 
  if C.is_conc_rhs c then 
    prevStep_conc me c
  else
    prevStep_abs me (C.id_of_t c) n

let killstep_of_fact me f = 
  FactMap.safeFind f me.fsm "Cex.killstep_of_fact"

let delta me c n k : fact list = 
  let _n = prevStep me c n in
  SM.safeFind k me.lifespan "delta: bad kvar" 
  |> List.filter (fun (m,_) -> _n <= m && m < n) 
  |> Misc.flap snd
  |> Misc.map (fun q -> Abs (k, q))

(************************************************************************)
(************************************************************************)
(************************************************************************)

let killerCands me c n : (int * (((Sy.t * fact) * A.pred)) list) list =
  foreach (C.kbindings_of_lhs c) begin fun (x, (vv, t, ras)) ->
    foreach ras begin function C.Kvar (su, k) ->
      foreach (delta me c n k) begin function (Abs (_, q) as f) ->
        let su' = Su.extend su (vv, A.eVar x)       in
        let p'  = A.substs_pred (Q.pred_of_t q) su' in 
        (x, f), p'
      end
    end |> Misc.flatten
  end |> Misc.flatten
  |> Misc.kgroupby (fst <+> snd <+> killstep_of_fact me)

(************************************************************************)
(******************** Lazy Explanations *********************************)
(************************************************************************)

let killedPred me c f =  
  match f, C.rhs_of_t c with
  | Abs (k, q), (_,_, [C.Kvar (su, k')])
    when k = k'
    -> A.substs_pred (Q.pred_of_t q) su
  | Conc cid, (_,_,[C.Conc p])
    when C.id_of_t c = cid
    -> p 
  | _ -> failwith "Counterexample.killed"

let getKillStep me c bgp iks =
  let iks = Misc.fsort fst iks in
  let ps  = iks |>: (snd <+> List.map snd <+> A.pAnd) in
  match TP.unsat_suffix me.tpc (C.senv_of_t c) bgp ps with
  | Some j when 0 <= j && j < List.length iks 
       -> List.nth iks j 
  | io -> let _ = F.printf 
                  "getKillStep failure: (cid = %d) (|iks| = %d) (io = %a)\n bgp = %a\nps  = %a\n"
                    (C.id_of_t c) 
                    (List.length iks) 
                    (Misc.pprint_maybe Misc.pprint_int) io
                    P.print bgp
                    (Misc.pprint_many_brackets true P.print) ps 
          in assertf "getKillStep"

let killinfo me = function
  | Conc cid -> me.n, cid
  | f        -> let n = killstep_of_fact me f in
                (n, IM.safeFind n me.scm "Cex.killinfo")

(* {{{ ORIGINAL: simply use unsat core.

let is_bot_killer = function
  | (f, p) when P.is_contra p -> Some f
  | _                         -> None


let getKillers_cands me c bgp cands =
  match cands, Misc.exists_maybe is_bot_killer cands with 
  | [], _ ->
      None
  | _, Some g -> 
      Some g 
  | _, _  -> 
      TP.unsat_core me.tpc (C.senv_of_t c) bgp cands 
      |> Misc.do_catch "ERROR: empty unsat core" List.hd
      |> some

let getKillers_fact (me: t) (f: fact) = 
  let n, cid     = killinfo me f                            in
  let c          = IM.safeFind cid me.cm "Cex.getKillers 3" in
  match killerCands me c n with []  -> (cid, None) | iks -> 
    let bgps       = C.preds_of_lhs (solutionAt me n) c
                     |> (++) [A.pNot (killedPred me c f)]   in
    let (j, cands) = getKillStep me c (A.pAnd bgps) iks     in
    let bgps'      = iks 
                   |> List.filter (fun (i,_) -> j < i)
                   |> Misc.flap   (snd <+> List.map snd)    in 
    (cid, getKillers_cands me c (A.pAnd (bgps ++ bgps')) cands)

let maxCubeSize = 1

let underApproxCubes me  (p:pred) (q:pred) (rs: ('a * pred) list) : 'a option =
  Misc.exists_maybe begin fun (f, fp) ->
    if SAT (p /\ fp) && UNSAT (p /\ fp /\ q) 
    then Some f
    else None
  end rs

}}} *)

let getKillers_cands me c p q rs =
  let env    = C.senv_of_t c in
  let contra = fun p -> TP.is_contra me.tpc env p in
  Misc.map_partial begin fun (f, fp) ->
    if contra (A.pAnd [p; fp; q]) && not (contra (A.pAnd [p; fp]))
    then Some f
    else None
  end rs

let getKillers_fact (me: t) (f: fact) = 
  let n, cid     = killinfo me f                            in
  let c          = IM.safeFind cid me.cm "Cex.getKillers 3" in
  match killerCands me c n with []  -> (cid, []) | iks -> 
    let bgps       = C.preds_of_lhs (solutionAt me n) c     in
    let killedp    = A.pNot (killedPred me c f)             in 
    let (j, cands) = getKillStep me c (A.pAnd bgps) iks     in
    let bgps'      = iks 
                   |> List.filter (fun (i,_) -> j < i)
                   |> Misc.flap   (snd <+> List.map snd)    in 
    (cid, getKillers_cands me c (A.pAnd (bgps ++ bgps')) killedp cands)

let rec explain me f =
  let cid, xfs = getKillers_fact me f in
  List.map (fun (x',f') -> Cause (x', f', cid, explain me f')) xfs

(********************************************************************)
(*********************** API ****************************************)
(********************************************************************)

(* API *)
let create s cs ctrace lifespan tpc =
  let scm    = scm_of_ctrace ctrace in
  { tpc      = tpc 
  ; s        = s 
  ; cm       = cs |>: Misc.pad_fst C.id_of_t |> IM.of_list 
  ; n        = 1 + Misc.list_max 0 (IM.domain scm)
  ; ctrace   = IM.map Misc.sort_and_compact ctrace 
  ; lifespan = lifespan
  ; fsm      = fsm_of_lifespan lifespan
  ; scm      = scm
  }  

(* API *)
let explain me c = 
  let cid0 = C.id_of_t c in
  let f0   = Conc cid0   in
  Cause (Sy.of_string "ERROR", f0, cid0, explain me f0)
