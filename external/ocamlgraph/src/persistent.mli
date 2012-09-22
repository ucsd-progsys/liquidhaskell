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

(* $Id: persistent.mli,v 1.13 2006-05-12 14:07:16 filliatr Exp $ *)

(** Persistent Implementations *)

open Sig

(** Signature of persistent graphs *)
module type S = sig

  (** Persistent Unlabeled Graphs *)
  module Concrete (V: COMPARABLE) : 
    Sig.P with type V.t = V.t and type V.label = V.t and type E.t = V.t * V.t

  (** Abstract Persistent Unlabeled Graphs *)
  module Abstract(V: ANY_TYPE) : Sig.P with type V.label = V.t

  (** Persistent Labeled Graphs *)
  module ConcreteLabeled (V: COMPARABLE)(E: ORDERED_TYPE_DFT) :
    Sig.P with type V.t = V.t and type V.label = V.t
	    and type E.t = V.t * E.t * V.t and type E.label = E.t

  (** Abstract Persistent Labeled Graphs *)
  module AbstractLabeled (V: ANY_TYPE)(E: ORDERED_TYPE_DFT) :
    Sig.P with type V.label = V.t and type E.label = E.t

end

(** Persistent Directed Graphs *)
module Digraph : S

(** Persistent Undirected Graphs *)
module Graph : S

