(*
 * Copyright © 2009-11 The Regents of the University of California. 
 * All rights reserved. 
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

(**
 * This module implements a module for representing and manipulating Qualifiers.
 * *)

type t 
module QSet : FixMisc.ESetType with type elt = t

val create          :  Ast.Symbol.t 
                    -> Ast.Symbol.t 
                    -> Ast.Sort.t 
                    -> (Ast.Symbol.t * Ast.Sort.t) list 
                    -> Ast.pred 
                    -> t 

val name_of_t       : t -> Ast.Symbol.t
val vv_of_t         : t -> Ast.Symbol.t
val pred_of_t       : t -> Ast.pred
val sort_of_t       : t -> Ast.Sort.t
val params_of_t     : t -> (Ast.Symbol.t * Ast.Sort.t) list (* Ast.Sort.t Ast.Symbol.SMap.t *)
val all_params_of_t : t -> (Ast.Symbol.t * Ast.Sort.t) list 
val vv_of_t         : t -> Ast.Symbol.t
val args_of_t       : t -> (Ast.Symbol.t * Ast.expr) list
val normalize       : t list -> t list
val inst            : t -> (Ast.Symbol.t * Ast.expr) list -> t
val print           : Format.formatter -> t -> unit
val print_args      : Format.formatter -> t -> unit
val expandPred      : Ast.Symbol.t -> Ast.expr list -> Ast.pred option


