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
 *)


(** This module implements various constraint validation and simplification 
 *  prepasses *)

module BS = BNstats
module F  = Format
module A  = Ast
module Co = Constants
module P  = A.Predicate
module E  = A.Expression
module So = A.Sort
module Q  = Qualifier
module PH = A.Predicate.Hash
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint

module Misc = FixMisc 
module IM = Misc.IntMap 

open Misc.Ops
let mydebug = false 

(***************************************************************)
(*********** Input Constraint & Solution Validation ************)
(***************************************************************)


(* 3a. check that lhs/rhs have same sort *)
let phase3a = 
  List.iter begin fun c ->
    let (vv1,t1,_) = C.lhs_of_t c in
    let (vv2,t2,_) = C.rhs_of_t c in
    if not (vv1 = vv2 && t1 = t2) then 
      let msg = "Invalid Constraints 3a (LHS/RHS sort mismatch)" in
      let _   = Format.printf "%s in \n %a " msg (C.print_t None) c in
      raise (C.BadConstraint (C.id_of_t c, C.tag_of_t c, msg))
  end

(* 3b. check that sorts are consistent across constraints. 
 * DEPRECATED, due to the following counterexample.
 * Suppose you have a function:

	concatMap :: forall a, t. (a -> [t]) -> [a] -> [t]
	concatMap f [] 	   = []
	concatMap f (y:ys) = (f y) ++ (concatMap f ys)

 * Now, "f" gets a template
	
	(y:a) -> [t]

 * And inside the body of concatMap, the recursive call 
 * creates a function subtyping on "f" 

	... |- (y:a) -> [t] <: (y:a) -> t

 * which after splitting gives a constraint

	...,(y:a) |- t <: t			(1)

 * Now, suppose you have a call to concatMap

	baz = concatMap (\x -> [x])

 * Here, concatMap is actually "instantiated" with a 
 * different type variable, so at this instance,

	concatMap :: ((y:b) -> [b]) -> [b] -> [b]

 * That is, a, t are instantiated with b, b. Now, the 
 * application creates another function subtyping, and 
 * this time you end up with 

	...,(y:b) |- b <: b			(2)

let phase3b cs =
  let memo = Hashtbl.create 17 in
  List.iter begin fun c ->
    let env = C.env_of_t c in
    let id  = C.id_of_t c in
    SM.iter begin fun x (_,t,_) ->
      if Hashtbl.mem memo x then 
        let xt = Hashtbl.find memo x in
        asserts (t = xt) "Invalid Constraints 3b: %d (%s is %s and %s)" 
          id (Sy.to_string x) (So.to_string t) (So.to_string xt)
      else 
        Hashtbl.replace memo x t
    end env
  end cs
*) 

(* 4. check that each tag has the same arity [a] *)
let phase4 a = 
  List.iter begin fun c ->
    if (a = List.length (fst (C.tag_of_t c))) then () else
      raise (C.BadConstraint (C.id_of_t c, C.tag_of_t c, "Tag Arity Error"))
  end

(* 5. check that all refinements are well-formed *)
let validate_vars env msg vs = 
  List.iter begin fun v -> 
    if not (SM.mem v env) then 
      let _ = F.printf "ERROR: out_of_scope variable %a (%s)" Sy.print v (Lazy.force msg) in
      failwith ("Out_of_scope: "^(Sy.to_string v))
  end vs 

let validate_pred env msg p = 
  P.support p 
  |> BS.time "validate_vars" (validate_vars env msg)

let validate_reft s env msg ((vv,t,_) as r) =
  let env = SM.add vv t env in
  r |> BS.time "preds_of_reft" (C.preds_of_reft s)
    |> List.iter (validate_pred env msg)

let phase5 s cs =
  Misc.filter begin fun c ->
    try
      let msg  = C.to_string c in
      let env  = C.senv_of_t c in
      let rhs  = C.rhs_of_t c  in
      List.iter (validate_pred env (lazy (msg^" BAD LHS"))) (C.preds_of_lhs s c);
      BS.time "valid rhs" (validate_reft s env (lazy (msg^"\n BAD RHS"))) rhs;
      true
    with ex -> begin 
      let id  = C.id_of_t c           in
      let tag = C.tag_of_t c          in
      let msg = Printexc.to_string ex in
      Format.printf "Phase5: exn = %s on constraint: %a \n" msg (C.print_t None) c;
      raise (C.BadConstraint (id, tag, msg))
    end
  end cs


(* API *)
let validate a s cs =
  cs >> phase3a 
  (* >> phase3b : RJ: this invariant need not hold! *) 
     >> phase4 a 
     |> phase5 s
     |> (fun cs' -> asserts (List.length cs = List.length cs') "Validation")

(******************************************************************************)
(******************* Validating Well-Formedness Constraints *******************)
(******************************************************************************)

let validate_wf wfvs = 
  C.reft_of_wf 
  <+> C.kvars_of_reft 
  <+> List.fold_left (fun wfvars (_, k) -> Sy.SSet.add k wfvars) wfvs
         (* if Sy.SSet.mem k wfvars then
           let _ = F.printf "ERROR: variable %a is checked for WF twice\n" Sy.print k in
             assert false
         else *)

(* API *)
let validate_wfs ws =
  ws |> List.fold_left begin fun (ws, wfvars) wf -> 
          (wf :: ws, validate_wf wfvars wf)
        end ([], Sy.SSet.empty) 
     |> fst


(***************************************************************)
(*********************** Constraint Profiling  *****************)
(***************************************************************)

let profile_cstr im c = 
  SM.fold begin fun _ (_,_,rs) ((a, b, c, d) as pfl) -> 
    match rs with [] -> (a+1, b, c, d+1)  | _::_ -> begin 
      List.fold_left begin fun (sz, csz, ksz, esz) r -> match r with 
        | C.Conc _  -> (sz+1, csz+1, ksz, esz) 
        | _         -> (sz+1, csz, ksz+1, esz)
      end pfl rs
    end
  end (C.env_of_t c) (0,0,0,0)
  |> fun pfl -> IM.add (C.id_of_t c) pfl im

let dump_profile im =
  let (tsz, tcsz, tksz, tesz) = 
    IM.fold begin fun i (sz, csz, ksz, esz) (tsz, tcsz, tksz, tesz) -> 
      Co.cLogPrintf Co.ol_solve
        "ctag %d: binds=%d, cbinds=%d, kbinds=%d, ebinds=%d \n" 
         i sz csz ksz esz;
      (tsz + sz, tcsz + csz, tksz + ksz, tesz + esz)
    end im (0,0,0,0) in
  Co.cLogPrintf Co.ol_solve_stats 
    "Total binds=%d, cbinds=%d, kbinds=%d, ebinds=%d \n" 
    tsz tcsz tksz tesz

let profile1 sri = 
  sri |> Cindex.to_list
      |> List.fold_left profile_cstr IM.empty
      |> dump_profile

let key_of_cstr c = 
  c |> C.env_of_t 
    |> C.bindings_of_env 
    |> List.map fst 
    |> List.map Sy.to_string 
    |> List.sort compare 
    |> String.concat "," 

let profile2 sri =
  sri |> Cindex.to_list
      |> Misc.groupby key_of_cstr 
      |> List.length
      |> fun n -> Co.cLogPrintf Co.ol_solve_stats "Constraint Clusters = %d \n" n

(* API *) 
let profile sri = 
  sri 
  >> profile1 
  >> profile2 
  |> ignore 

