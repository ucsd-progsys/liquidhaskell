(*
 * Copyright © 2009-12 The Regents of the University of California. All rights reserved. 
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
(* Counterexample Generation (cf. Lahiri-Vanegue, VMCAI 2011) **) 
(***************************************************************)

type t 

type kvar     = Ast.Symbol.t
type fact     = Abs of kvar * Qualifier.t | Conc of FixConstraint.id
type step     = int 

(* [k |-> [(i0, [q_i0_1...]),...]] 
 * where q_i0_1... are killed at timestep i0 for kvar k sorted by step *)
type lifespan = (step * Qualifier.t list) list Ast.Symbol.SMap.t 

(* [cid |-> i0,...] cid is selected at steps i0... by solver *)
type ctrace  = step list FixMisc.IntMap.t 

type cex     

val create  :  FixConstraint.soln       (* assumes           *) 
            -> FixConstraint.t list     (* all constraints   *)
            -> ctrace                   
            -> lifespan 
            -> TpNull.Prover.t          (* tp context        *)
            -> t

val explain : t -> FixConstraint.t -> cex
val print_cex : Format.formatter -> cex -> unit
