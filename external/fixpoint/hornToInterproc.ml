
module F  = Format
module BS = BNstats
module Co = Constants 
module SM = Misc.StringMap 
module H  = Ast.Horn
module Misc = FixMisc open Misc.Ops


let tmpname1 = "tmp"

(***************************************************************************)
(************************* Parse Horn Clauses ******************************)
(***************************************************************************)

let clean f =
  Misc.map_lines_of_file f tmpname1 begin fun s ->
    if String.length s > 3 && String.sub s 0 3 = "hc(" then
        let ss = Misc.chop s ", " in
        match ss with
        | [s1; s2; _] -> Printf.sprintf "%s, %s).\n\n" s1 s2
        | ss          -> assertf "bad string: %s" (String.concat "####" ss)
    else ""
  end;
  tmpname1

let parse f : H.t list = 
  let ic = f |> clean >> Errorline.startFile |> open_in in
  let rv = Lexing.from_channel ic |> HornParse.horns HornLex.token in
  let _  = close_in ic in
  rv

(****************************************************************************)
(******************* Preprocess HC to get global information ****************)
(****************************************************************************)

type t = {
  aritym : int SM.t;            (* k -> arity *)
  bindm  : string list SM.t;    (* k -> local bindings *)
  argn   : int;                 (* max-fun-args across all ks *)
  cm     : H.t list SM.t;       (* k -> cs *)
}

let create (cs: H.t list) : t =
  let cm = cs |> Misc.kgroupby (fun ((k,_),_) -> k) 
              |> List.fold_left (fun cm (k,cs) -> SM.add k cs cm) SM.empty in
  let aritym = SM.map (function ((k, xs),_)::_ -> 
                         let n = List.length xs in
                         (* let _ = Printf.printf "Arity(%s) using %s is %d \n" k
                         (String.concat "," xs) n in *)
                      n) cm in
  let bindm  = SM.map ((Misc.flap H.support) <+> Misc.sort_and_compact) cm in
  let argn   = SM.fold (fun _ a n -> max a n) aritym 0 in
  { aritym = aritym; bindm = bindm; argn = argn; cm = cm }

(****************************************************************************)
(**************************** Generic Sequencers ****************************)
(****************************************************************************)

let gen f sep xs =
  xs |> Misc.map f |> String.concat sep

let geni f sep xs = 
  xs |> Misc.mapi f |> String.concat sep

let defn x n =
  geni (fun i _ -> Printf.sprintf "%s%d : int" x i) ", " (Misc.range 0 n)

(****************************************************************************)
(********************************* Translation ******************************)
(****************************************************************************)

let tx_gd = function
  | H.C p       -> Printf.sprintf "    assume %s;" (Misc.fsprintf Ast.Predicate.print p)
  | H.K (k, xs) -> Printf.sprintf "%s\n    () = %s(%s);" 
                     (geni (Printf.sprintf "    a%d = %s;") "\n" xs)
                     k
                     (geni (fun i _ -> Printf.sprintf "a%d" i) "," xs)

let tx_hd = function 
  | "error", _ -> "    fail;"
  | _, xs      -> Printf.sprintf "    assume %s;" 
                     (geni (fun i x -> Printf.sprintf " z%d == %s " i x) " and " xs)

let tx_t k (head, guards) : string =
  Printf.sprintf "  if brandom then\n%s\n%s\n  else" (gen tx_gd "\n" guards) (tx_hd head)

let tx_def me = function
  | "error" -> 
      ""
  | k -> 
      let n = try SM.find k me.aritym with Not_found -> assertf "ERROR:no arity for %s" k in
      let _ = Printf.printf "Arity(%s) := %d \n" k n in 
      Printf.sprintf "proc %s(%s) returns ()" k (defn "z" n) 

let tx_k me (k, cs) =  
  Printf.sprintf 
"
%s
var %s, %s;
begin
%s
    halt;
  %s  
end
" 
(tx_def me k) 
(defn "a" me.argn) 
(gen (Printf.sprintf "%s : int") ", " (SM.find k me.bindm)) 
(gen (tx_t me) "\n" cs)
(gen (fun _ -> "endif;") " " cs)

let rewrite_eq s = 
  if Misc.is_substring s "assume" then 
    Misc.replace_substring " = " " == " s 
  else s

let tx cs = 
  let me = create cs in
  me.cm 
  |> Misc.sm_to_list
  |> List.map (tx_k me)
  |> String.concat "\n\n"
  |> Misc.flip Misc.chop "\n" 
  |> List.map rewrite_eq
  |> String.concat "\n"

(***************************************************************************)
(***************************** Output Clauses ******************************)
(***************************************************************************)

let dump f cs =
  cs >> Format.printf "*************Horn Clauses************\n\n%a\n\n\n" (Misc.pprint_many true "\n" H.print)
     |> tx 
     >> Format.printf "***********Interproc Program*********\n\n%s\n\n\n" 
     |> Misc.write_to_file (f^".ipc")

let usage = "hornToInterproc.native [filename.pl]"

let main usage = 
  print_now "\n \n \n \n \n";
  print_now "========================================================\n";
  print_now "© Copyright 2009 Regents of the University of California.\n";
  print_now "All Rights Reserved.\n";
  print_now "========================================================\n";
  print_now (Sys.argv |> Array.to_list |> String.concat " ");
  print_now "\n========================================================\n";
  let fs = ref [] in
  let _  = Arg.parse Co.arg_spec (fun s -> fs := s::!fs) usage in
  match !fs with 
  | [f] -> parse f |> dump f 
  | _   -> assertf "I choke on too many/few files!" 

let _ = main usage
