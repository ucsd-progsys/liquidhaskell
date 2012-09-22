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

(* $Id: imperative.mli,v 1.18 2006-05-12 14:07:16 filliatr Exp $ *)

(** Imperative Implementations *)

open Sig

(** Signature of imperative graphs *)
module type S = sig

  (** Imperative Unlabeled Graphs *)
  module Concrete (V: COMPARABLE) : 
    Sig.I with type V.t = V.t and type V.label = V.t and type E.t = V.t * V.t

  (** Abstract Imperative Unlabeled Graphs *)
  module Abstract(V: ANY_TYPE) : 
    Sig.IM with type V.label = V.t and type E.label = unit

  (** Imperative Labeled Graphs *)
  module ConcreteLabeled (V: COMPARABLE)(E: ORDERED_TYPE_DFT) :
    Sig.I with type V.t = V.t and type V.label = V.t 
	    and type E.t = V.t * E.t * V.t and type E.label = E.t

  (** Abstract Imperative Labeled Graphs *)
  module AbstractLabeled (V: ANY_TYPE)(E: ORDERED_TYPE_DFT) :
    Sig.IM with type V.label = V.t and type E.label = E.t

end

(** Imperative Directed Graphs *)

module Digraph : sig 
  include S   

  (** Imperative Unlabeled, bidirectional graph (gives predecessors in
      constant time) *)
  module ConcreteBidirectional (V: COMPARABLE) : 
    Sig.I with type V.t = V.t and type V.label = V.t and type E.t = V.t * V.t 
end

(** Imperative Undirected Graphs *)
module Graph : S

(** Imperative graphs implemented as adjacency matrices *)
module Matrix : sig

  module type S = sig

    (** Vertices are integers in [0..n-1]. 
        A vertex label is the vertex itself. 
        Edges are unlabeled. *)

    include Sig.I with type V.t = int and type V.label = int
		  and type E.t = int * int

    (** Creation. graphs are not resizeable: size is given at creation time.
        Thus [make] must be used instead of [create] *)
    val make : int -> t

    (** Note: [add_vertex] and [remove_vertex] have no effect *)

  end

  module Digraph : S
    (** Imperative Directed Graphs implemented with adjacency matrices *)

  module Graph : S
    (** Imperative Undirected Graphs implemented with adjacency matrices *)

end

