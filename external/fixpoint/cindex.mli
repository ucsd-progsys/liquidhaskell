(*
 * Copyright © 2009 The Regents of the University of California. All rights reserved. 
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

(***************************************************************)
(**** This module implements constraint indexing ***************)
(***************************************************************)

type t
type wkl

(** indexing and dependencies *)
val to_list      : t -> FixConstraint.t list 

(* val to_live_list : t -> FixConstraint.t list *)
val create       : Ast.Symbol.t list -> FixConstraint.dep list -> FixConstraint.t list -> t 
val deps         : t -> FixConstraint.t -> FixConstraint.t list
val slice        : t -> t 
val slice_wf     : t -> FixConstraint.wf list -> FixConstraint.wf list

(** worklist manipulation *)
val wpush        : t -> wkl -> FixConstraint.t list -> wkl 
val wpop         : t -> wkl -> FixConstraint.t option * wkl
val winit        : t -> wkl

(** printing *)
val print        : Format.formatter -> t -> unit 


(***************************************************************)
(*********** Some Operations for Constraint Cones **************)
(***************************************************************)

val data_cones: FixConstraint.t list -> FixConstraint.id -> FixConstraint.tag Ast.Cone.t

