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
 *)

type t

type rd = Bnd of Ast.Symbol.t * Ast.Subst.t | Lhs of Ast.Subst.t | Grd | Junk

val empty        : t
val remove       : t -> FixConstraint.refa list -> t
val add          : t -> FixConstraint.t list -> t 
val print_stats  : t -> unit
val cone_ids     : t -> FixConstraint.id list
val writes       : t -> FixConstraint.refa list -> FixConstraint.id list
val reads        : t -> FixConstraint.refa list -> FixConstraint.id list
val k_reads      : t -> FixConstraint.id -> FixConstraint.refa -> rd list
val filter_kvars : (FixConstraint.refa -> bool) -> t -> FixConstraint.refa list
val is_single_wr : t -> FixConstraint.refa -> bool
val is_single_rd : t -> FixConstraint.refa -> bool
