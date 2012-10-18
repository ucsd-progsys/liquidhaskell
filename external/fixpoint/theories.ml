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

module So = Ast.Sort
module Sy = Ast.Symbol

open FixMisc.Ops


type appDef  = { sy_name  : Sy.t
               ; sy_sort  : So.t
               ; sy_emb   : Z3.context -> Z3.sort list -> Z3.ast list -> Z3.ast
               }

type sortDef = { so_name  : Ast.Sort.tycon
               ; so_arity : int
               ; so_emb   : Z3.context -> Z3.sort list -> Z3.sort 
               }

(* API *)
let sort_name d = d.so_name
let sym_name d  = d.sy_name
let sym_sort d  = d.sy_sort

(***************************************************************************)
(******************** Theory of Sets ***************************************)
(***************************************************************************)

let set_tycon  = So.tycon "Set_Set"
let t_set a    = So.t_app set_tycon [a]

let set_set : sortDef = 
  { so_name  = set_tycon 
  ; so_arity = 1 
  ; so_emb   = fun c -> function 
                 [t] -> Z3.mk_set_sort c t
                 | _ -> assertf "Set_set: type mismatch"
  }  

let set_emp : appDef  = 
  { sy_name  = Sy.of_string "Set_emp"
  ; sy_sort  = So.t_func 1 [t_set (So.t_generic 0); So.t_bool]
  ; sy_emb   = fun c ts es -> match ts, es with
                 | [t], [e] -> Z3.mk_eq c e (Z3.mk_empty_set c t)
                 | _        -> assertf "Set_emp: type mismatch"
  }

let set_sng : appDef  = 
  { sy_name = Sy.of_string "Set_sng"
  ; sy_sort = So.t_func 1 [So.t_generic 0; t_set (So.t_generic 0)] 
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e] -> Z3.mk_set_add c (Z3.mk_empty_set c t) e
                 | _        -> assertf "Set_sng: type mismatch"
  }


let set_mem : appDef  = 
  { sy_name = Sy.of_string "Set_mem"
  ; sy_sort = So.t_func 1 [So.t_generic 0; t_set (So.t_generic 0); So.t_bool] 
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e;es] -> Z3.mk_set_member c e es 
                 | _           -> assertf "Set_mem: type mismatch"
  }

let set_cup : appDef  = 
  { sy_name = Sy.of_string "Set_cup"
  ; sy_sort = So.t_func 1 [t_set (So.t_generic 0); t_set (So.t_generic 0); t_set (So.t_generic 0)]
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e1;e2] -> Z3.mk_set_union c [| e1; e2 |] 
                 | _            -> assertf "Set_cup: type mismatch"
  }

let set_cap : appDef  = 
  { sy_name = Sy.of_string "Set_cap"
  ; sy_sort = So.t_func 1 [t_set (So.t_generic 0); t_set (So.t_generic 0); t_set (So.t_generic 0)] 
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e1;e2] -> Z3.mk_set_intersect c [| e1; e2 |] 
                 | _            -> assertf "Set_cap: type mismatch"
  }

let set_dif : appDef  = 
  { sy_name = Sy.of_string "Set_dif"
  ; sy_sort = So.t_func 1 [t_set (So.t_generic 0); t_set (So.t_generic 0); t_set (So.t_generic 0)]
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e1;e2] -> Z3.mk_set_difference c e1 e2 
                 | _            -> assertf "Set_dif: type mismatch"
  }

let set_sub : appDef =
  { sy_name = Sy.of_string "Set_sub"
  ; sy_sort = So.t_func 1 [t_set (So.t_generic 0); t_set (So.t_generic 0); So.t_bool] 
  ; sy_emb  = fun c ts es -> match ts, es with
                 | [t], [e1;e2] -> Z3.mk_set_subset c e1 e2 
                 | _            -> assertf "Set_dif: type mismatch"
  }

(* API *)
let set_theory = ([set_set], [set_emp; set_sng; set_mem; set_cup; set_cap; set_dif; set_sub])

(***************************************************************************)
(********* Wrappers Around Z3 Constructors For Last-Minute Checking ********)
(***************************************************************************)

let app_sort_arity def = match So.func_of_t def.sy_sort with
  | Some (n,_,_) -> n
  | None         -> assertf "Theories: app with non-function symbol %s" 
                    (Sy.to_string def.sy_name)

let check_app_arities def tArgs eArgs = match So.func_of_t def.sy_sort with
  | Some (n, ts,_) 
     -> asserts (n = List.length tArgs)  
          "Theories: app with mismatched sorts %s" (Sy.to_string def.sy_name);
        asserts (List.length ts = List.length eArgs) 
          "Theories: app with mismatched args %s" (Sy.to_string def.sy_name) 
  | None         
     -> assertf "Theories: app with non-function symbol %s" 
          (Sy.to_string def.sy_name)


(* API *)
let mk_thy_app def c ts es = 
  check_app_arities def ts es;
  def.sy_emb c ts es

(* API *)
let mk_thy_sort def c ts = 
  asserts (List.length ts = def.so_arity) 
    "Theories: app with mismatched sorts %s" (So.tycon_string def.so_name);
  def.so_emb c ts 

(* API *)
let theories () = set_theory

(*
let symbols  () = 
  Misc.map_partial begin function 
    | Sym {sy_name = x; sy_sort = t} -> Some (x, t) 
    | _                              -> None
  end (theories ())

*)
