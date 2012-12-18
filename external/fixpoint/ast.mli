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

(**
 * This module implements a DAG representation for expressions and 
 * predicates: each sub-predicate or sub-expression is paired with
 * a unique int ID, which enables constant time hashing. 
 * However, one must take care when using DAGS:
 * (1) they can only be constructed using the appropriate functions
 * (2) when destructed via pattern-matching, one must discard the ID
 *)

(*******************************************************)
(********************** Base Logic  ********************)
(*******************************************************)

module Cone : sig 
  type 'a t = Empty | Cone of ('a * 'a t) list
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module Sort :
  sig
    type loc = 
      | Loc  of string 
      | Lvar of int
      | LFun

    type tycon
    type t    
    type sub
   
    val tycon       : string -> tycon
    val tycon_string: tycon -> string

    val to_string   : t -> string
    val print       : Format.formatter -> t -> unit
   
    val t_num       : t
    val t_obj       : t
    val t_bool      : t
    val t_int       : t
    val t_generic   : int -> t
    val t_ptr       : loc -> t
    val t_func      : int -> t list -> t
    val t_app       : tycon -> t list -> t
    (* val t_fptr      : t *)
   
    val is_bool     : t -> bool
    val is_int      : t -> bool
    val is_func     : t -> bool
    val app_of_t    : t -> (tycon * t list) option 
    val func_of_t   : t -> (int * t list * t) option
    val ptr_of_t    : t -> loc option
 
    val compat      : t -> t -> bool
    val empty_sub   : sub
    val unifyWith   : sub -> t list -> t list -> sub option 
    val unify       : t list -> t list -> sub option
    val apply       : sub -> t -> t
    val generalize  : t list -> t list
    val sub_args    : sub -> (int * t) list
    (* val check_arity : int -> sub -> bool *)
  end

module Symbol : 
  sig 
    type t 
    module SMap         : FixMisc.EMapType with type key = t
    module SSet         : FixMisc.ESetType with type elt = t
    val mk_wild         : unit -> t  
    val of_string       : string -> t
    val to_string       : t -> string 
    val is_wild_any     : t -> bool
    val is_wild_fresh   : t -> bool
    val is_wild         : t -> bool
    val print           : Format.formatter -> t -> unit
    val value_variable  : Sort.t -> t
    val is_value_variable : t -> bool
    val suffix          : t -> string -> t
  end

module Constant :
  sig
    type t = Int of int
    val to_string : t -> string
    val print : Format.formatter -> t -> unit
  end

type tag  (* externally opaque *)

type brel = Eq | Ne | Gt | Ge | Lt | Le 

type bop  = Plus | Minus | Times | Div | Mod    (* NOTE: For "Mod" 2nd expr should be a constant or a var *)

type expr = expr_int * tag 

and expr_int =
  | Con  of Constant.t
  | Var  of Symbol.t
  | App  of Symbol.t * expr list
  | Bin  of expr * bop * expr  
  | Ite  of pred * expr * expr
  | Fld  of Symbol.t * expr             (* NOTE: Fld (s, e) == App ("field"^s,[e]) *) 
  | Cst  of expr * Sort.t 
  | Bot
  | MExp of expr list
  | MBin of expr * bop list * expr 
  
and pred = pred_int * tag

and pred_int =
  | True
  | False
  | And  of pred list
  | Or   of pred list
  | Not  of pred
  | Imp  of pred * pred
  | Iff  of pred * pred
  | Bexp of expr
  | Atom of expr * brel * expr 
  | MAtom of expr * brel list * expr
  | Forall of ((Symbol.t * Sort.t) list) * pred

(* Constructors : expressions *)
val eTim : expr * expr -> expr
val eInt : int -> expr
val eCon : Constant.t -> expr
val eMExp : expr list -> expr
val eMod : expr * int -> expr
val eModExp : expr * expr -> expr
val eVar : Symbol.t -> expr
val eApp : Symbol.t * expr list -> expr
val eBin : expr * bop * expr -> expr 
val eMBin : expr * bop list * expr -> expr 
val eIte : pred * expr * expr -> expr
val eFld : Symbol.t * expr -> expr
val eCst : expr * Sort.t -> expr
(* Constructors : predicates *)
val pTrue  : pred
val pFalse : pred
val pAtom  : expr * brel * expr -> pred
val pMAtom : expr * brel list * expr -> pred
val pAnd   : pred list -> pred
val pOr    : pred list -> pred
val pNot   : pred -> pred
val pImp   : (pred * pred) -> pred
val pIff   : (pred * pred) -> pred
val pBexp  : expr -> pred
val pForall: ((Symbol.t * Sort. t) list) * pred -> pred
val pEqual : expr * expr -> pred

val neg_brel : brel -> brel

module Expression : 
sig
  module Hash : Hashtbl.S with type key = expr 
  
  val print     : Format.formatter -> expr -> unit
  val show      : expr -> unit
  val to_string : expr -> string
  
  val unwrap    : expr -> expr_int
  val support   : expr -> Symbol.t list
  val subst     : expr -> Symbol.t -> expr -> expr 
  val map       : (pred -> pred) -> (expr -> expr) -> expr -> expr 
  val iter      : (pred -> unit) -> (expr -> unit) -> expr -> unit 
end
 

module Predicate :
sig
  module Hash : Hashtbl.S with type key = pred 
 
  val print     : Format.formatter -> pred -> unit
  val show      : pred -> unit
  val to_string : pred -> string

  val unwrap    : pred -> pred_int
  val support   : pred -> Symbol.t list
  val subst     : pred -> Symbol.t -> expr -> pred
  val map       : (pred -> pred) -> (expr -> expr) -> pred -> pred 
  val iter      : (pred -> unit) -> (expr -> unit) -> pred -> unit 
  val is_contra : pred -> bool
  val is_tauto  : pred -> bool
end

module Subst : 
  sig
    type t
    val empty                : t
    val is_empty             : t -> bool
    val extend               : t -> (Symbol.t * expr) -> t
    val compose               : t -> t -> t
    val of_list              : (Symbol.t * expr) list -> t
    val simultaneous_of_list : (Symbol.t * expr) list -> t
    val to_list              : t -> (Symbol.t * expr) list
    val print                : Format.formatter -> t -> unit
    val apply                : t -> Symbol.t -> expr option
  end


module Horn :
  sig
    type pr = string * string list
    type gd = C of pred | K of pr
    type t  = pr * gd list 
    val print: Format.formatter -> t -> unit
    val support: t -> string list
  end

val print_stats    : unit -> unit
val fixdiv         : pred -> pred
val zero           : expr
val one            : expr
val bot            : expr

val symm_pred      : pred -> pred
val unify_pred     : pred -> pred -> Subst.t option
val substs_expr    : expr -> Subst.t -> expr
val substs_pred    : pred -> Subst.t -> pred 
val simplify_pred  : pred -> pred
val conjuncts      : pred -> pred list

val sortcheck_expr : (Symbol.t -> Sort.t option) -> expr -> Sort.t option
val sortcheck_pred : (Symbol.t -> Sort.t option) -> pred -> bool
val sortcheck_app  : (Symbol.t -> Sort.t option) -> Sort.t option -> Symbol.t -> expr list -> (Sort.sub * Sort.t) option

val into_of_expr   : expr -> int option

