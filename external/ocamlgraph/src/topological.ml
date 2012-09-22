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

(*i $Id: topological.ml,v 1.5 2004-02-20 14:37:41 signoles Exp $ i*)

module type G = sig
  type t
  module V : Sig.HASHABLE
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val in_degree : t -> V.t -> int
end

module Make(G: G) = struct

  module H = Hashtbl.Make(G.V)

  let fold f g acc =
    let degree = H.create 997 in
    let todo = Queue.create () in
    let rec walk acc = 
      try
	let v = Queue.pop todo in
	let acc = f v acc in
	G.iter_succ 
	  (fun x-> let d = H.find degree x in
	   if d=1 then Queue.push x todo
	   else H.replace degree x (d-1))
	  g v; 
	walk acc
      with Queue.Empty -> acc
    in
    G.iter_vertex 
      (fun v -> 
	 let d = G.in_degree g v in 
	 if d = 0 then Queue.push v todo
	 else H.add degree v d)
      g;
    walk acc

  let iter f g = fold (fun v () -> f v) g ()

end
