module BS = BNstats
module SM = Ast.Symbol.SMap
module Co = Constants 
module C  = FixConstraint
module F  = Format
module Misc = FixMisc open Misc.Ops


(*
let parse_string str =
  let lb = Lexing.from_string str in
    ArithParser.aexpr ArithLexer.token lb

let token_list_of_string s =
  let lb = Lexing.from_string s in
  let rec helper l = 
    try 
      let t = ArithLexer.token lb in
      if t = ArithParser.EOF then List.rev l else helper (t::l)
    with _ -> List.rev l
  in helper []

let eval_string env str = ArithInterpreter.eval env (parse_string str) 
*)

(*****************************************************************)
(********************* Command line options **********************)
(*****************************************************************)

let parse f = 
  let _  = Errorline.startFile f in
  let ic = open_in f in
  let rv = Lexing.from_channel ic |> FixParse.defs FixLex.token in
  let _  = close_in ic in
  rv

let read_inputs usage = 
  print_now "\n \n \n \n \n";
  print_now "========================================================\n";
  print_now "© Copyright 2009 Regents of the University of California.\n";
  print_now "All Rights Reserved.\n";
  print_now "========================================================\n";
  print_now (Sys.argv |> Array.to_list |> String.concat " ");
  print_now "\n========================================================\n";
  let fs = ref [] in
  let _  = Arg.parse Co.arg_spec (fun s -> fs := s::!fs) usage in
  let fq = !fs |> BS.time "parse" (Misc.flap parse) |> FixConfig.create in 
  (!fs, fq)
