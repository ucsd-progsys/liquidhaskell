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


(** read a set of constraints, solve, and dump out the solution *)

module CX  = Counterexample



module BS  = BNstats
module SM  = Ast.Symbol.SMap
module Co  = Constants 
module C   = FixConstraint
module F   = Format
module T   = Toplevel
module PA  = PredAbs
module SPA = Solve.Make (PA)
module Cg  = FixConfig

module Misc = FixMisc open Misc.Ops

(*****************************************************************)
(********************* Hooking into Solver ***********************)
(*****************************************************************)

let print_raw_cs ppf = function
  | [] -> F.fprintf ppf "SAT \n \n \n"
  | cs -> F.fprintf ppf "UNSAT [%s] \n \n \n" (Misc.map_to_string (C.id_of_t <+> string_of_int) cs)

let save_raw fname cs s = 
  Misc.with_out_formatter fname begin fun ppf ->
    F.fprintf ppf "%a \n" print_raw_cs cs; 
    F.fprintf ppf "%a \n" PA.print s;
    F.fprintf ppf "@.";
    F.print_flush ()
  end

let save_crash fname (id, tag, msg) =
  Misc.with_out_formatter fname begin fun ppf ->
    F.fprintf ppf "CRASH %d (%s)\n" id msg;
    F.fprintf ppf "//%a\n" C.print_tag tag;
    F.fprintf ppf "@.";
    F.print_flush ()
  end

let solve ac  = 
  let _         = print_now "Fixpoint: Creating  CI\n" in
  let ctx, s    = BS.time "create" SPA.create ac None in
  let _         = print_now "Fixpoint: Solving \n" in
  let s, cs',_  = BS.time "solve" (SPA.solve ctx) s in
  
  let _         = print_now "Fixpoint: Saving Result \n" in
  let _         = BS.time "save" (save_raw !Co.out_file cs') s in
  let _         = print_now "Fixpoint: Saving Result DONE \n" in
  cs'

let dump_solve ac = 
  try 
    let cs' = solve { ac with Cg.bm = SM.map PA.mkbind ac.Cg.bm } in
    let _   = BNstats.print stdout "Fixpoint Solver Time \n" in
    match cs' with 
    | [] -> (F.printf "\nSAT\n" ; exit 0)
    | _  -> (F.printf "\nUNSAT\n" ; exit 1)
  with (C.BadConstraint (id, tag, msg)) -> begin
    Format.printf "Fixpoint: Bad Constraint! id = %d (%s) tag = %a \n" 
    id msg C.print_tag tag;
    save_crash !Co.out_file (id, tag, msg); 
  end

(*****************************************************************)
(********************* Generate Imp Program **********************)
(*****************************************************************)

let dump_imp a = 
  (List.map (fun c -> Cg.Cst c) a.Cg.cs ++ List.map (fun c -> Cg.Wfc c) a.Cg.ws)
  |> ToImp.render F.std_formatter
  |> fun _ -> exit 1 

(*****************************************************************)
(***************** Generate Simplified Constraints ***************)
(*****************************************************************)

let hook_simplify_ts = function
  | "andrey" -> List.map Simplification.simplify_t
                <+> List.filter (not <.> Simplification.is_tauto_t)
                <+> Simplification.simplify_ts
  | "jhala"  -> FixSimplify.simplify_ts
  (* put other transforms here *)
  | _        -> id

let simplify_ts cs = hook_simplify_ts !Co.dump_simp cs

let dump_simp ac = 
  let ac = {ac with Cg.cs = simplify_ts ac.Cg.cs; Cg.bm = SM.empty} in
  Misc.with_out_formatter !Co.save_file (fun ppf -> Cg.print ppf ac)

(*
let dump_simp ac = 
  (* let ac    = {ac with Cg.cs = simplify_ts ac.Cg.cs; Cg.bm = SM.empty; Cg.qs = []} in *)
  let ac    = {ac with Cg.cs = simplify_ts ac.Cg.cs; Cg.bm = SM.empty} in
  Misc.with_out_formatter !Co.save_file (fun ppf -> Cg.print ppf ac)

  let ctx,_ = BS.time "create" SPA.create ac None in
  let s0    = PA.empty (* PA.create ac None *) in 
  let _     = BS.time "save" (SPA.save !Co.save_file ctx) s0 in
  exit 1
*)

(*****************************************************************)
(*********************** Main ************************************)
(*****************************************************************)

let usage = "Usage: fixpoint.native <options> [source-files]\noptions are:"

let main () =
  let cfg  = usage |> Toplevel.read_inputs |> snd in 
  if !Co.dump_imp then 
    dump_imp cfg 
  else if !Co.dump_smtlib then
    ToSmtLib.dump_smtlib cfg
  else if !Co.dump_simp <> "" then 
    dump_simp cfg
  else
    dump_solve cfg 



let _ = main ()
