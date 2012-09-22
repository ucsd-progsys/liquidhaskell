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

(* $Id: gmap.ml,v 1.1 2004-10-20 09:59:56 signoles Exp $ *)

module Vertex
  (G_Init : sig
     type t
     module V : Sig.HASHABLE
     val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
   end)
  (G_Dest : sig
     type t
     type vertex
     val empty : unit -> t
     val add_vertex : t -> vertex -> t
   end) =
struct
  
  module H = Hashtbl.Make(G_Init.V)
    
  let vertices = H.create 97

  let convert_vertex f x =
    try 
      H.find vertices x
    with Not_found ->
      let x' = f x in
      H.add vertices x x';
      x'

  let map f g =
    H.clear vertices;
    G_Init.fold_vertex
      (fun x g -> G_Dest.add_vertex g (convert_vertex f x)) 
      g (G_Dest.empty ())

end

module Edge
  (G_Init : sig
     type t
     module E : Sig.HASHABLE
     val fold_edges_e : (E.t -> 'a -> 'a) -> t -> 'a -> 'a
   end)
  (G_Dest : sig
     type t
     type edge
     val empty : unit -> t
     val add_edge_e : t -> edge -> t
   end) =
  Vertex
    (struct include G_Init module V = E let fold_vertex = fold_edges_e end)
    (struct include G_Dest type vertex = edge let add_vertex = add_edge_e end)
