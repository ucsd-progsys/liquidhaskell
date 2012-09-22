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

(* $Id: gmap.mli,v 1.1 2004-10-20 09:59:56 signoles Exp $ *)

(** Graph mapping *)

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
   end) :
sig

  val map : (G_Init.V.t -> G_Dest.vertex) -> G_Init.t -> G_Dest.t
    (** [map f g] applies [f] to each vertex of [g] and so builds a new graph
      based on [g] *)

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
   end) :
sig

  val map : (G_Init.E.t -> G_Dest.edge) -> G_Init.t -> G_Dest.t
    (** [map f g] applies [f] to each edge of [g] and so builds a new graph
      based on [g] *)

end
