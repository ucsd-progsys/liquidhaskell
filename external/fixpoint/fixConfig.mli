(* This module deals with top-level parsing of fq files and such *)

(*
exception UnmappedKvar of Ast.Symbol.t
*)
type qbind   = Qualifier.t list
type solbind = Ast.Symbol.t * ((Ast.Symbol.t * (Ast.expr list)) list)
type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of FixConstraint.t
          | Wfc of FixConstraint.wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of solbind
          | Qul of Qualifier.t
          | Dep of FixConstraint.dep
          | Kut of Ast.Symbol.t
          | IBind of int * Ast.Symbol.t * FixConstraint.reft  

type 'bind cfg = { 
   a     : int                               (* Tag arity                            *)
 ; ts    : Ast.Sort.t list                   (* New sorts, now = []                  *)
 ; ps    : Ast.pred list                     (* New axioms, now = []                 *)
 ; cs    : FixConstraint.t list              (* Implication Constraints              *)
 ; ws    : FixConstraint.wf list             (* Well-formedness Constraints          *)
 ; ds    : FixConstraint.dep list            (* Constraint Dependencies              *)
 ; qs    : Qualifier.t list                  (* Qualifiers                           *)
 ; kuts  : Ast.Symbol.t list                 (* "Cut"-Kvars, which break cycles      *)
 ; bm    : 'bind Ast.Symbol.SMap.t           (* Initial Sol Bindings                 *)
 ; uops  : Ast.Sort.t Ast.Symbol.SMap.t      (* Globals: measures + distinct consts) *)
 ; cons  : Ast.Symbol.t list                 (* Distinct Constants, defined in uops  *)
 ; assm  : FixConstraint.soln                (* Seed Solution -- must be a fixpoint over constraints *)
}


module type DOMAIN = sig
  type t
  type bind
  val empty        : t 
  (* val meet         : t -> t -> t *)
  val min_read     : t -> FixConstraint.soln
  val read         : t -> FixConstraint.soln
  val read_bind    : t -> Ast.Symbol.t -> bind
  val top          : t -> Ast.Symbol.t list -> t
  val refine       : t -> FixConstraint.t -> (bool * t)
  val unsat        : t -> FixConstraint.t -> bool
  val create       : bind cfg -> FixConstraint.soln option -> t
  val print        : Format.formatter -> t -> unit
  val print_stats  : Format.formatter -> t -> unit
  val dump         : t -> unit
  val ctr_examples : t -> FixConstraint.t list -> FixConstraint.t list -> Counterexample.cex list 
  val mkbind       : qbind -> bind
end


module type SIMPLIFIER = sig
  val simplify_ts: FixConstraint.t list -> FixConstraint.t list
end

val empty     : 'a cfg 
val create    : deft list -> qbind cfg
val print     : Format.formatter -> 'a cfg -> unit
val create_raw:  Ast.Sort.t list 
              -> Ast.Sort.t Ast.Symbol.SMap.t 
              -> Ast.pred list 
              -> int 
              -> FixConstraint.dep list 
              -> FixConstraint.t list 
              -> FixConstraint.wf list 
              -> Qualifier.t list
              -> Ast.Symbol.t list
              -> FixConstraint.soln 
              -> 'a cfg
