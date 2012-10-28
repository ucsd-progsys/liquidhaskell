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


(** This module implements a fixpoint solver *)
module BS = BNstats
module F  = Format
module A  = Ast
module Co = Constants
module P  = A.Predicate
module E  = A.Expression
module So = A.Sort
module Su = A.Subst
module Q  = Qualifier
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint
module Ci = Cindex
module PP = Prepass
module Cg = FixConfig
module Th = Theories

module Misc = FixMisc open Misc.Ops


let mydebug = false 

type t = {
   sri : Ci.t
 ; ws  : C.wf list
 ; tt  : Timer.t
   
 (* Stats *)
 ; stat_refines        : int ref
 ; stat_cfreqt         : (int * bool, int) Hashtbl.t 
}

module type SOLVER = sig
  type soln
  type bind
  val create    : bind Cg.cfg -> FixConstraint.soln option -> (t * soln)
  val solve     : t -> soln -> (soln * (FixConstraint.t list) * Counterexample.cex list) 
  val save      : string -> t -> soln -> unit 
  val read      : soln -> FixConstraint.soln
  val min_read  : soln -> FixConstraint.soln
  val read_bind : soln -> Ast.Symbol.t -> bind
  val cone      : t -> FixConstraint.id -> FixConstraint.tag Ast.Cone.t
  (* val meet   : soln -> soln -> soln  *)
end

module Make (Dom : Cg.DOMAIN) = struct
  type soln     = Dom.t
  type bind     = Dom.bind
  let min_read  = Dom.min_read
  let read      = Dom.read
  let read_bind = Dom.read_bind  
(* let meet = Dom.meet *)


(*************************************************************)
(********************* Stats *********************************)
(*************************************************************)

let hashtbl_incr_frequency t k = 
  let n = try Hashtbl.find t k with Not_found -> 0 in
  Hashtbl.replace t k (n+1)

let hashtbl_print_frequency t = 
  Misc.hashtbl_to_list t 
  |> Misc.kgroupby (fun ((k,b),n) -> (n,b))
  |> List.map (fun ((n,b), xs) -> (n, b, List.map (fst <+> fst) xs))
  |> List.sort compare
  |> List.iter begin fun (n, b, xs) -> 
       Co.logPrintf "ITERFREQ: %d times (ch = %b) %d constraints %s \n"
         n b (List.length xs) (Misc.map_to_string string_of_int xs) 
     end

(***************************************************************)
(************************ Debugging/Stats **********************)
(***************************************************************)

let print_constr_stats ppf cs = 
  let cn   = List.length cs in
  let scn  = List.length (List.filter C.is_simple cs) in
  F.fprintf ppf "#Constraints: %d (simple = %d) \n" cn scn

let print_solver_stats ppf me = 
  print_constr_stats ppf (Ci.to_list me.sri); 
  F.fprintf ppf "#Iterations = %d\n" !(me.stat_refines);
  F.fprintf ppf "Iteration Frequency: \n"; 
    hashtbl_print_frequency me.stat_cfreqt;
  F.fprintf ppf "Iteration Periods: @[%a@] \n" Timer.print me.tt

let dump me s = 
  Co.cLogPrintf Co.ol_solve_stats "%a \n" print_solver_stats me;
  Co.cLogPrintf Co.ol_solve_stats "%a \n" Dom.print_stats s;
  Dom.dump s

let log_iter_stats me s =
  (if Co.ck_olev Co.ol_insane then Co.logPrintf "%a" Dom.print s);
  (if !(me.stat_refines) mod 100 = 0 then 
     let msg = Printf.sprintf "num refines=%d" !(me.stat_refines) in 
     let _   = Timer.log_event me.tt (Some msg) in
     let _   = Co.logPrintf "%s" msg in 
     let _   = Co.logPrintf "%a \n" Dom.print_stats s in
     let _   = Format.print_flush () in
     ());
  ()

(***************************************************************)
(******************** Iterative Refinement *********************)
(***************************************************************)

let is_solved s c = 
  let sol = read s in
  c |> C.rhs_of_t 
    |> C.kvars_of_reft
    |> List.map (sol <.> snd)
    |> List.for_all ((=) [])

let refine_constraint s c =
  try BS.time "refine" (Dom.refine s) c with ex ->
    let _ = F.printf "constraint refinement fails with: %s\n" (Printexc.to_string ex) in
    let _ = F.printf "Failed on constraint:\n%a\n" (C.print_t None) c in
    assert false

let update_worklist me s' c w' = 
  c |> Ci.deps me.sri 
    |> Misc.filter (not <.> is_solved s')
    |> Ci.wpush me.sri w'

let rec acsolve me w s =
  let _ = log_iter_stats me s in
  let _ = Misc.display_tick () in
  match Ci.wpop me.sri w with 
  | (None,_) -> 
      let _ = Timer.log_event me.tt (Some "Finished") in 
      s 
  | (Some c, w') ->
      let _        = me.stat_refines += 1             in 
      let (ch, s') = BS.time "refine" (refine_constraint s) c in
      let _        = hashtbl_incr_frequency me.stat_cfreqt (C.id_of_t c, ch) in  
      let _        = Co.bprintf mydebug "iter=%d id=%d ch=%b %a \n" 
                      !(me.stat_refines) (C.id_of_t c) ch C.print_tag (C.tag_of_t c) in
      let w''      = if ch then update_worklist me s' c w' else w' in 
      acsolve me w'' s' 


let unsat_constraints me s =
  me.sri |> Ci.to_list |> List.filter (Dom.unsat s)

(***************************************************************)
(****************** Pruning Unconstrained Vars *****************)
(***************************************************************)

let rhs_ks cs =
  cs  |> Misc.flap (Misc.compose C.kvars_of_reft C.rhs_of_t)
      |> List.fold_left (fun rhss (_, kv) -> Sy.SSet.add kv rhss) Sy.SSet.empty

let unconstrained_kvars cs =
  let rhss = rhs_ks cs in
  cs  |> Misc.flap C.kvars_of_t
      |> List.map snd
      |> List.filter (fun kv -> not (Sy.SSet.mem kv rhss))

let true_unconstrained sri s =
  sri |> Ci.to_list 
      >> (fun _ -> Co.logPrintf "Fixpoint: true_unconstrained Step 2 \n")
      |> unconstrained_kvars
      >> (fun _ -> Co.logPrintf "Fixpoint: true_unconstrained Step 2 \n")
      |> Dom.top s
      >> (fun _ -> Co.logPrintf "Fixpoint: true_unconstrained Step 3 \n")
(* 
let true_unconstrained sri s = 
  if !Co.true_unconstrained then 
    let _ = Co.logPrintf "Fixpoint: Pruning unconstrained kvars \n" 
    in true_unconstrained sri s
  else 
    let _ = Co.logPrintf "Fixpoint: NOT Pruning unconstrained kvars \n" 
    in s
*)

(* API *)
let solve me s = 
  let _  = Co.logPrintf "Fixpoint: Validating Initial Solution \n" in
  (* let _ = F.printf "create: SOLUTION \n %a \n" Dom.print s in *)
  let _  = BS.time "Prepass.profile" PP.profile me.sri in
  let _  = print_now "\nBEGIN: Fixpoint: Trueing Unconstrained Variables \n" in
  let s  = s |> (!Co.true_unconstrained <?> BS.time "Prepass.true_unconstr" (true_unconstrained me.sri)) in
  let _  = print_now "\nDONE: Fixpoint: Trueing Unconstrained Variables \n" in
  (* let _ = F.printf "create: SOLUTION1 \n %a \n" Dom.print s in *)
  let _  = print_now "\nBEGIN: Fixpoint: Initialize Worklist \n" in
  let w  = BS.time "Cindex.winit" Ci.winit me.sri in 
  let _  = print_now "\nDONE: Fixpoint: Initialize Worklist \n" in
  let _  = print_now "\nBEGIN: Fixpoint Refinement Loop \n" in
  let s  = BS.time "Solve.acsolve"  (acsolve me w) s in
  let _  = print_now "\nDONE: Fixpoint Refinement Loop \n" in
  (* let _ = F.printf "create: SOLUTION2 \n %a \n" Dom.print s in *)
  let _  = BS.time "Solve.dump" (dump me) s in
  let _  = Co.logPrintf "Fixpoint: Testing Solution \n" in
  let u  = BS.time "Solve.unsatcs" (unsat_constraints me) s in
  let _  = if u != [] then F.printf "Unsatisfied Constraints:\n %a" (Misc.pprint_many true "\n" (C.print_t None)) u in
  let cx = if !Co.cex && Misc.nonnull u then Dom.ctr_examples s (Ci.to_list me.sri) u else [] in
  (s, u, cx)

let global_symbols cfg = 
     (SM.to_list cfg.Cg.uops)                                           (* specified globals *) 
  ++ (Theories.theories () |> snd |>: (Th.sym_name <*> Th.sym_sort))    (* theory globals *)

(* API *)
let create cfg kf =
  let gts = global_symbols cfg in
  let sri = cfg.Cg.cs
            >> Co.logPrintf "Pre-Simplify Stats\n%a" print_constr_stats
            |> BS.time  "Constant Env" (List.map (C.add_consts_t gts))
            |> BS.time  "Simplify" FixSimplify.simplify_ts
            >> Co.logPrintf "Post-Simplify Stats\n%a" print_constr_stats
            |> BS.time  "Ref Index" Ci.create cfg.Cg.kuts cfg.Cg.ds
            |> (!Co.slice <?> BS.time "Slice" Ci.slice) in
  let ws  = cfg.Cg.ws
            |> (!Co.slice <?> BS.time "slice_wf" (Ci.slice_wf sri))
            |> BS.time  "Constant EnvWF" (List.map (C.add_consts_wf gts))
            |> PP.validate_wfs in
  let cfg = { cfg with Cg.cs = Ci.to_list sri; Cg.ws = ws } in
  let s   = if !Constants.dump_simp <> "" then Dom.empty else Dom.create cfg kf in
  let _   = Co.logPrintf "DONE: Dom.create\n" in
  let _   = Ci.to_list sri
            |> BS.time "Validate" (PP.validate cfg.Cg.a (Dom.read s)) in
  let _   = Co.logPrintf "DONE: PP.validate \n" in
  ({ sri          = sri
   ; ws           = ws
   (* stat *)
   ; tt           = Timer.create "fixpoint iters"
   ; stat_refines = ref 0
   ; stat_cfreqt  = Hashtbl.create 37
   }, s)
   >> (fun _ -> Co.logPrintf "DONE: Solve.create\n")

(* API *)
let save fname me s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" Ci.print me.sri;
  F.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" (C.print_wf None)) me.ws;
  F.fprintf ppf "@[%a@] \n" Dom.print s;
  close_out oc

(* API *)
let cone me = Cindex.data_cones (Ci.to_list me.sri)

end
