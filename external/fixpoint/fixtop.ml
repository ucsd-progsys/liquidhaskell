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

module SM = Ast.Symbol.SMap
module Co = Constants 
module C  = FixConstraint
module F  = Format
(*module Si = Simplification *)
module Misc = FixMisc 
open Misc.Ops

let _ = FixLex.token (Lexing.from_string "int");;

let parse_string f = f FixLex.token <.> Lexing.from_string 


let dump cs ws =
  Format.printf "Printing Out Parsed Constraints \n \n \n" ;
  Format.printf "%a" (Misc.pprint_many true "\n" (FixConstraint.print_t None)) cs; 
  Format.printf "\n \n";
  Format.printf "%a" (Misc.pprint_many true "\n" (FixConstraint.print_wf None)) ws;
  Format.printf "\n \n"

let usage = "Usage: fixtop <options> [source-files]\noptions are:"

let main () = print_string "Hello World \n"

(*
let main () =
  let fs, config = Toplevel.read_inputs usage in
  let cs = config.C.cs in
  let ws = config.C.ws in
  let cs = 
    if !Co.simplify_t then
      Misc.map_partial begin fun t -> 
        let st = Si.simplify_t t in
	if Si.is_tauto_t st then None else Some st
      end cs |> Si.simplify_ts
    else cs in
    begin
      match !Co.latex_file with
	| Some f ->
	    let out = open_out f in
	      ToLatex.to_latex out cs ws;
	      close_out out
	| None -> ()
    end;
  (*
    begin
      match !Co.armc_file with
	| Some f -> 
	    let out = open_out f in
	      Printf.fprintf out "%% %s\n" (String.concat ", " fs);
	      ToHC.to_dataflow_armc out cs ws sol;
	      close_out out
	| None -> ()
    end;
  *)
    (*
    begin
      match !Co.horn_file with
	| Some f -> 
	    let out = open_out f in
	      Printf.fprintf out "%% %s\n" (String.concat ", " fs);
	      ToHC.to_horn out cs ws sol;
	      close_out out
	| None -> ()
    end;
    *)
    begin
      match !Co.q_armc_file with
	| Some f -> 
	    let out = open_out f in
	      Printf.fprintf out "%% %s\n" (String.concat ", " fs);
	      ToQARMC.to_qarmc out cs ws;
	      close_out out
	| None -> ()
    end;
(*
    begin
      match !Co.raw_horn_file with
	| Some f -> 
	    let out = open_out f in
	      Printf.fprintf out "%% %s\n" (String.concat ", " fs);
	      ToRawHorn.to_raw_horn out cs ws sol;
	      close_out out
	| None -> ()
    end;
*)
    begin
      match !Co.dot_file with
	| Some f -> 
	    let oc = open_out f in
	      ToDot.to_dot oc cs;
	      close_out oc
	| None -> ()
    end
*)

let _ = main ()
