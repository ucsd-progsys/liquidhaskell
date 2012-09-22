(*
 * Copyright © 2008 The Regents of the University of California. All rights reserved.
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

module F = Format
module C = Constants

let mydebug = false 

(****************************************************************)
(************* SCC Ranking **************************************)
(****************************************************************)

module Int : Graph.Sig.COMPARABLE with type t = int * string =
struct
   type t = int * string 
   let compare = compare
   let hash = Hashtbl.hash
   let equal = (=)
end

module G = Graph.Imperative.Digraph.Concrete(Int)

module SCC = Graph.Components.Make(G)    

(* Use of Graphviz *)

let io_to_string = function 
  | Some i -> string_of_int i 
  | None -> "*"

module DotGraph =
struct
   type t = G.t
   module V = G.V
   module E = G.E
   let iter_vertex = G.iter_vertex
   let iter_edges_e = G.iter_edges_e
   let graph_attributes g = [`Size (11.0, 8.5); `Ratio (`Float 1.29)]
   let default_vertex_attributes g = [`Shape `Box]
   let vertex_name (i,_) = string_of_int i (* Printf.sprintf "V_%d" i *) 
   let vertex_attributes (_,s) = [`Label s]
   let default_edge_attributes g = []
   let edge_attributes e = []
   let get_subgraph v = None
end

module Dot = Graph.Graphviz.Dot(DotGraph) 

let dump_graph s g = 
  let oc = open_out (s^".dot") in
  Dot.output_graph oc g; 
  close_out oc

let int_s_to_string ppf (i,s) = 
  F.fprintf ppf "(%d,%s)" i s 

let scc_print g a = 
  C.bprintf mydebug "dep graph: vertices= %d, sccs= %d \n" (G.nb_vertex g) (Array.length a);
  C.bprintf mydebug "scc sizes: \n";
  Array.iteri begin fun i xs -> 
    C.bprintf mydebug "%d : [%a] \n" i (FixMisc.pprint_many false "," int_s_to_string) xs
  end a;
  C.cprintf C.ol_scc "\n"

let make_graph s f is ijs = 
  let g = G.create () in
  let _ = List.iter (fun i -> G.add_vertex g (i, (f i))) is in
  let _ = List.iter (fun (i,j) -> G.add_edge g (i,(f i)) (j,(f j))) ijs in
  let _ = if !Constants.dump_graph then dump_graph s g in
  g
 
(* Given list [(u,v)] returns a numbering [(ui,ri)] s.t. 
 * 1. if ui,uj in same SCC then ri = rj
 * 2. if ui -> uj then ui >= uj *)
let scc_rank s f is ijs = 
  let g = BNstats.time "making_graph" (make_graph s f is) ijs in
  let a = SCC.scc_array g in
  let _ = scc_print g a in
  let sccs = FixMisc.array_to_index_list a in
  FixMisc.flap (fun (i,vs) -> List.map (fun (j,_) -> (j,i)) vs) sccs

(*
let g1 = [(1,2);(2,3);(3,1);(2,4);(3,4);(4,5)];;
let g2 = [(0,1);(1,2);(2,0);(1,3);(4,3);
          (5,6);(5,7);(6,9);(7,9);(7,8);(8,5)];;
let g3 = (6,2)::g2;;
let g4 = (2,6)::g2;;
  
let n1 = make_scc_num g1 ;;
let n2 = make_scc_num g2 ;;
let n3 = make_scc_num g3 ;;
let n4 = make_scc_num g4 ;; *)

(*
type fc_id = int option 
type subref_id = int 

module WH = 
  Heaps.Functional(struct 
      type t = subref_id * int * (int * bool * fc_id)
      let compare (_,ts,(i,j,k)) (_,ts',(i',j',k')) =
        if i <> i' then compare i i' else
          if ts <> ts' then -(compare ts ts') else
            if j <> j' then compare j j' else 
              compare k' k
    end)
*)

