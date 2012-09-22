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

(** k-coloring of undirected graphs.

    A k-coloring of a graph g is a mapping c from nodes to \{1,...,k\} such
    that c(u)<>c(v) for any edge u-v in g. *)

exception NoColoring

(** Graph coloring for graph with integer marks. *)

module type GM = sig
  type t
  val nb_vertex : t -> int
  module V : Sig.COMPARABLE
  val out_degree : t -> V.t -> int
  val iter_vertex : (V.t -> unit) -> t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  module Mark : sig
    val get : V.t -> int
    val set : V.t -> int -> unit
  end
end

module Mark(G : GM) : sig

  val coloring : G.t -> int -> unit
    (** [coloring g k] colors the nodes of graph [g] using k colors,
	assigning the marks integer values between 1 and k.
        raises [NoColoring] when there is no possible coloring.

        The graph marks may be partially set before starting; the meaning of
        initial values is as follows:
	- 0: a node to be colored
	- any value between 1 and k: a color already assigned
	- any value greater than k: a node to be ignored *)

end

(** Graph coloring for graphs without marks *)

module type G = sig
  type t
  val nb_vertex : t -> int
  module V : Sig.COMPARABLE
  val out_degree : t -> V.t -> int
  val iter_vertex : (V.t -> unit) -> t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t  -> 'a -> 'a
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
end

module Make(G: G) : sig

  module H : Hashtbl.S with type key = G.V.t
    (** hash tables used to store the coloring *)

  val coloring : G.t -> int -> int H.t
    (** [coloring g k] colors the graph [g] with [k] colors and returns the
        coloring as a hash table mapping nodes to their colors. *)

end
