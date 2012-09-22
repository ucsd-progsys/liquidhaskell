module C = FixConstraint
module StrSet = Set.Make (struct type t = string let compare = compare end)
module StrStrSet = Set.Make (struct type t = StrSet.t let compare = StrSet.compare end)

module S2 = StrSet
module S3 = StrStrSet
module Misc = FixMisc open Misc.Ops


module V = struct
  type t = string
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module E = struct
  type t = string
  let compare = Pervasives.compare
  let default = ""
end


module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)

module Display = struct
  include G
  let vertex_name v = "\"" ^ String.escaped v ^ "\""
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes e = [`Label (G.E.label e)]
  let get_subgraph _ = None
end

module DotOutput = Graph.Graphviz.Dot(Display)

module SCC = Graph.Components.Make(G) 

let vertices_of_graph g = G.fold_vertex (fun v vs -> v::vs) g []
let edges_e_of_graph g = G.fold_edges_e (fun e es -> e::es) g []

let set_of_strings = List.fold_left (fun s x -> StrSet.add x s) StrSet.empty

let set_to_string default s = 
  if StrSet.is_empty s then default else StrSet.elements s |> List.map String.escaped |> String.concat ", "

let edges_e_to_graph es = List.fold_left (fun g e -> G.add_edge_e g e) G.empty es

(* k_1, ..., k_n <: k_0 depends on l_1, ..., l_m <: l_0 iff l_0 = k_i for some 1 \leq i \leq n *)


let t_to_dep t = 
  let env = C.env_of_t t in
  let lhs = C.lhs_of_t t in
  let rhs = C.rhs_of_t t in
  let tag = try string_of_int (C.id_of_t t) with _ -> 
    failure "ERROR: t_to_edge: anonymous constraint %s" (C.to_string t) in
  let src =
    C.kvars_of_reft lhs :: List.map (fun b -> snd b |> C.kvars_of_reft) (C.bindings_of_env env) |> 
	List.flatten |> List.map snd |> List.map Ast.Symbol.to_string |> set_of_strings in
  let dst = C.kvars_of_reft rhs |> List.map snd |> List.map Ast.Symbol.to_string |> set_of_strings in
    src, tag, dst

let sccs_to_dot g prefix =
  let n, scc_of = SCC.scc g in
  let vs = vertices_of_graph g in
    Printf.printf "%s #scc = %d\n" prefix n;
    for i = 0 to n-1 do
      let scc, rest = List.partition (fun v -> scc_of v = i) vs in
      let g' = List.fold_left (fun g'' v -> G.remove_vertex g'' v) g rest in 
      let out = open_out (Printf.sprintf "/tmp/%s-scc-%d.dot" prefix i) in
	Printf.printf "%s scc %d %s\n" prefix i (String.concat ", " scc);
	DotOutput.output_graph out g';
	close_out out
    done


let mk_dep_graph ts =
  let ds' = List.map t_to_dep ts in
  let ds = List.map (fun (src, tag, dst) ->
		       (if StrSet.is_empty src then StrSet.singleton "start" else src),
		       tag,
		       (if StrSet.is_empty dst then StrSet.singleton "error" else dst)
		    ) ds' in
  let g = 
    List.map
      (fun (src, tag, dst) ->
	 Misc.map_partial
	   (fun (src', tag', dst') ->
	      let inter = StrSet.inter dst src' in
		if StrSet.is_empty inter then 
		  None
		else 
		  begin
		    Printf.printf "self loop %s\n" tag;
		    Some(G.E.create tag (set_to_string "" inter) tag') (* tag depends on tag' via inter   *)
		  end
	   ) ds
      ) ds |> List.flatten |> edges_e_to_graph in
  let srcs = List.fold_left (fun xs (src, tag, dst) -> src::xs) [] ds' in

(*
  let veanu = 
    List.fold_left (fun xs src ->
		      S3.fold (fun x ys -> 
				 ys |> S3.add (S2.diff x src) |> S3.add (S2.diff src x) |> S3.add (S2.inter x src) 
			      ) xs S3.empty 
		   ) (List.hd srcs |> S3.singleton) (List.tl srcs) in
*)
  let oc = open_out "/tmp/dep.dot" in
    DotOutput.output_graph oc g;
    close_out oc;
    sccs_to_dot g "dep";
    print_endline "start deps";
    List.iter (fun (src, tag, dst) -> 
		 Printf.printf "%s <: %s  (%s)\n" (set_to_string "" src) (set_to_string "" dst) tag) ds;
    print_endline "end deps";
    print_endline "start dep graph";
    List.iter (fun e -> 
		 Printf.printf "%s - %s -> %s\n" (G.E.src e) (G.E.label e) (G.E.dst e)) (edges_e_of_graph g);
    print_endline "end dep graph"
(*
    Printf.printf "Veanu %d sets\n%s\n" 
      (S3.cardinal veanu)
      (S3.fold (fun x s -> 
		  (Printf.sprintf "{%s}" (set_to_string "empty" x))::s
	       ) veanu [] |> String.concat ",\n")
*)


let other_graph ts =
  let deps = List.map t_to_dep ts in
  let srcs, dsts = List.map (fun (s, _, d) -> s, d) deps |> List.split in
  let es = List.map (fun (src, tag, dst) ->
		       G.E.create (set_to_string "start" src) tag (set_to_string "error" dst) 
		    ) deps in
  let es' = List.fold_left (fun es'' dst ->
			      Misc.map_partial (fun src -> 
						  if StrSet.diff dst src |> StrSet.is_empty then
						    Some (G.E.create (set_to_string "error" dst) "" (set_to_string "start" src))
						  else
						    None
					       ) srcs ++ es''
			   ) es dsts in
  let g = List.fold_left (fun g e -> G.add_edge_e g e) G.empty es' in
    g

let t_to_edge t = 
  let srcs', tag, dsts' = t_to_dep t in
  let srcs = if StrSet.is_empty srcs' then ["start"] else StrSet.elements srcs' in
  let dsts = if StrSet.is_empty dsts' then ["error"] else StrSet.elements dsts' in
    List.fold_left (fun es src -> List.map (G.E.create src tag) dsts ++ es) [] srcs


    

let to_dot oc ts =
  let _ =  List.fold_left (fun g e -> G.add_edge_e g e ) G.empty (List.map t_to_edge ts |> List.flatten) in
  let g = other_graph ts in
  let vs = G.fold_vertex (fun v vs' -> v::vs') g [] in
  let n, scc_of = SCC.scc g in
    DotOutput.output_graph oc g;
    Printf.printf "#scc = %d\n" n;
    for i = 0 to n-1 do
      let scc, rest = List.partition (fun v -> scc_of v = i) vs in
      let g' = List.fold_left (fun g'' v -> G.remove_vertex g'' v) g rest in 
      let out = open_out (Printf.sprintf "/tmp/scc-%d.dot" i) in
	Printf.printf "scc %d %s\n" i (String.concat ", " scc);
	DotOutput.output_graph out g';
	close_out out
    done;
    mk_dep_graph ts
