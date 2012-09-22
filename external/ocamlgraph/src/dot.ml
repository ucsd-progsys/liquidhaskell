(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2007                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id:$ *)

(** Parser for DOT file format *)

open Dot_ast

module Parse 
  (B : Builder.S)
  (L : sig 
     val node : node_id -> attr list -> B.G.V.label
       (** how to build the node label out of the set of attributes *)
     val edge : attr list -> B.G.E.label 
       (** how to build the edge label out of the set of attributes *)
   end) =
struct

  let create_graph dot =
    let nodes = Hashtbl.create 97 in
    let node g id l =
      try
	g, Hashtbl.find nodes id
      with Not_found ->
	let n = B.G.V.create (L.node id l) in
	Hashtbl.add nodes id n;
	B.add_vertex g n, n
    in
    List.fold_left
      (fun g s -> match s with
	| Node_stmt (id, al) ->
	    let g,_ = node g id al in g
	| Edge_stmt (NodeId id, nl, al) ->
	    let el = L.edge al in
	    let g,vn = node g id [] in
	    List.fold_left
	      (fun g m -> match m with
		| NodeId idm -> 
		    let g,vm = node g idm [] in
		    let e = B.G.E.create vn el vm in
		    B.add_edge_e g e
		| NodeSub _ -> 
		    g)
	      g nl
	| _ ->
	    g)
      (B.empty ()) 
      dot.stmts

  let parse f =
    let c = open_in f in
    let lb = Lexing.from_channel c in
    let dot = 
      try
	Dot_parser.file Dot_lexer.token lb 
      with Parsing.Parse_error ->
	let n = Lexing.lexeme_start lb in
	failwith (Printf.sprintf "Dot.parse: parse error character %d" n)
    in
    close_in c;
    create_graph dot

end
