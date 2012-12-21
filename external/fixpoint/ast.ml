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

(* random touch *)

module F  = Format
module Misc = FixMisc
open Misc.Ops
module SM = Misc.StringMap

let mydebug = false

module Cone = struct
  type 'a t = Empty | Cone of ('a * 'a t) list

  let rec map f = function 
    | Empty    -> Empty
    | Cone xcs -> Cone (List.map (f <**> map f) xcs)
end 

module Sort =
  struct
    type loc = 
      | Loc  of string 
      | Lvar of int
      | LFun 

    type tycon = string

    type t =
      | Int
      | Bool
      | Obj
      | Var of int              (* type-var *)
      | Ptr of loc              (* c-pointer *)
      | Func of int * t list    (* type-var-arity, in-types @ [out-type] *)
      | Num                     (* kind, for numeric tyvars -- ptr(loc(s)) -- *)
      | App of tycon * t list   (* type constructors *)

    type sub = { locs: (int * string) list; 
                 vars: (int * t) list; }

   
    let tycon_string x = x
    (*
    let is_loc_string s = 
      let re = Str.regexp "[a-zA-Z]+[0-9]+" in 
      Str.string_match re s 0
    
    let loc_of_string = fun s -> let _ = asserts (is_loc_string s) in Loc s
    let loc_of_index  = fun i -> Lvar i
    *)

    let t_num       = Num 
    let t_obj       = Obj
    let t_bool      = Bool
    let t_int       = Int
    let t_generic   = fun i -> let _ = asserts (0 <= i) "t_generic: %d" i in Var i
    let t_ptr       = fun l -> Ptr l
    let t_func      = fun i ts -> Func (i, ts)
    let tycon s     = s 
    
    (* let tycon_re    = Str.regexp "[A-Z][0-9 a-z A-Z '.']"
     * function | s when Str.string_match tycon_re s 0 -> s  
                | s -> assertf "Error: Invalid tycon: %s" s 
     *)

    let t_app c ts  = App (c, ts)

    let loc_to_string = function
      | Loc s  -> s
      | Lvar i -> string_of_int i
      | LFun   -> "<fun>"

    let rec to_string = function
      | Var i        -> Printf.sprintf "@(%d)" i
      | Int          -> "int"
      | Bool         -> "bool"
      | Obj          -> "obj"
      | Num          -> "num"
      | Ptr l        -> loc_to_string l 
                        (* Printf.sprintf "ptr(%s)" (loc_to_string l) *)
      | Func (n, ts) -> ts |> List.map to_string 
                           |> String.concat " ; " 
                           |> Printf.sprintf "func(%d, [%s])" n 
      | App (c, ts)  -> ts |> List.map to_string_arg 
                           |> String.concat " " 
                           |> Printf.sprintf "%s %s" c 
    
    and to_string_arg t = match t with 
      | App (_, _) -> Printf.sprintf "(%s)" (to_string t)
      | _          -> to_string t

    let to_string_short = function
      | Func _ -> "func"
   (* | Ptr _  -> "ptr" *)
      | t      -> to_string t      

    let print fmt t = 
      t |> to_string 
        |> Format.fprintf fmt "%s"

    let sub_to_string {locs = ls; vars = vs} =
      let lts = fun (i, s) -> Printf.sprintf "(%d := %s)" i s in
      let vts = fun (i, t) -> Printf.sprintf "(%d := %s)" i (to_string t) in
      Printf.sprintf "locs := %s, vars := %s \n" 
        (String.concat "" (List.map lts ls)) 
        (String.concat "" (List.map vts vs)) 

    let rec map f = function 
      | Func (n, ts) -> Func (n, List.map (map f) ts)
      | App  (c, ts) -> App  (c, List.map (map f) ts)
      | t            -> f t

    let rec fold f b = function
      | Func (n, ts) as t -> List.fold_left (fold f) (f b t) ts
      | t                 -> f b t

    let subs_tvar ts = 
      map begin function 
          | Var i -> Misc.do_catchf "ERROR: subs_tvar" (List.nth ts) i
          | t     -> t
      end

    let is_bool = function
      | Bool -> true
      | _    -> false

    let is_int = function
      | Int -> true
      | _   -> false

    let is_func = function
      | Func _ -> true
      | _   -> false

    let app_of_t = function
      | App (c, ts) -> Some (c, ts) 
      | _           -> None


    let func_of_t = function
      | Func (i, ts) -> let (xts, t) = ts |> Misc.list_snoc |> Misc.swap in 
                        Some (i, xts, t)
      | _            -> None

    let ptr_of_t = function
      | Ptr l -> Some l
      | _     -> None

    (* Sleazy Hack for C pointers. Make this go away... *)

    let compat t1 t2 = match t1, t2 with
      | Int, (Ptr _) -> true
      | (Ptr _), Int -> true
      | _            -> t1 = t2

    (* {{{ 
    let concretize ts = function 
      | Func (n, ats) when n = List.length ts -> 
          Func (n, List.map (subs_tvar ts) ats)
      | _ -> 
          assertf "ERROR: bad application" 

    let is_monotype t = 
      fold (fun b t -> b && (match t with Var _ -> false | _ -> true)) true t
    }}} *)


    let lookup_var = fun s i -> try Some (List.assoc i s.vars) with Not_found -> None
    let lookup_loc = fun s j -> try Some (List.assoc j s.locs) with Not_found -> None
    
    let rec unifyt s = function 
      | Num,_ | _, Num -> None
      | ct, (Var i) 
      | (Var i), ct 
        (* when ct != Bool *) -> 
          begin match lookup_var s i with 
          | Some ct' when ct = ct' -> Some s
          | Some _                 -> None
          | None                   -> Some {s with vars = (i,ct) :: s.vars}
          end
      | Ptr LFun, Ptr _ 
      | Ptr _, Ptr LFun -> Some s
      | Ptr (Loc cl), Ptr (Lvar j)
      | Ptr (Lvar j), Ptr (Loc cl) ->
          begin match lookup_loc s j with 
          | Some cl' when cl' = cl -> Some s
          | Some _                 -> None
          | None                   -> Some {s with locs = (j,cl) :: s.locs}
          end
      
      | App (c1, t1s), App (c2, t2s) 
        when c1 = c2 && List.length t1s = List.length t2s ->
          Misc.maybe_fold unifyt s (List.combine t1s t2s)
      
      | (t1, t2) when t1 = t2 -> 
          Some s
      | _        -> None
   
    let empty_sub = {vars = []; locs = []}
   
    let unifyWith s ats cts =
      let _ = asserts (List.length ats = List.length cts) "ERROR: unify sorts" in
      List.combine ats cts 
      |> Misc.maybe_fold unifyt s 
      (* >> (fun so -> Printf.printf "unify: [%s] ~ [%s] = %s \n" 
                      (String.concat "; " (List.map to_string ats))
                      (String.concat "; " (List.map to_string cts))
                      (match so with None -> "NONE" | Some s -> sub_to_string s))
       *)

    let unify = unifyWith empty_sub

    let apply s = 
      map begin fun t -> match t with
          | Var i        -> (match lookup_var s i with Some t' -> t' | _ -> t)
          | Ptr (Lvar j) -> (match lookup_loc s j with Some l -> Ptr (Loc l) | _ -> t)
          | _            -> t
      end

    let rec fold f acc t = match t with
      | Var _ | Int  | Bool | Obj | Num | Ptr _ 
        -> f acc t 
      | Func (_, ts) | App (_, ts) 
        -> List.fold_left (fold f) (f acc t) ts 
      
    let vars_of_t = fold begin fun acc -> function 
      | Var i -> i :: acc 
      | _     -> acc
    end []
    
    let locs_of_t = fold begin fun acc -> function 
      | Ptr (Loc l) -> l :: acc 
      | _           -> acc
    end []
    
    let subst_locs_vars lim = map begin function
      | Ptr (Loc l) when SM.mem l lim -> Var (SM.find l lim)
      | t                             -> t
    end

    (* API *)
    let generalize ts = 
      let locs = ts |> Misc.flap locs_of_t |> Misc.sort_and_compact       in
      let idx  = ts |> Misc.flap vars_of_t |> Misc.list_max (-1) |> (+) 1 in 
      let lim  = Misc.index_from idx locs |>: Misc.swap |> SM.of_list          in
      List.map (subst_locs_vars lim) ts

    (* API *)
    let sub_args s = List.sort compare s.vars

    (* API *)
    let check_arity n s = s.vars |>: fst |> Misc.sort_and_compact |> List.length |> (=) n
      (* if ... then s else assertf "Type Inst. With Wrong Arity!" *)

  end

module Symbol = 
  struct 
    type t = string
    
    let mk_wild =
      let t,_ = Misc.mk_int_factory () in
      t <+> string_of_int <+> (^) "~A"
    
    let is_wild_fresh s = s = "_"
    let is_wild_any   s = s.[0] = '~'
    let is_wild_pre   s = s.[0] = '@'
    let is_wild s       = is_wild_fresh s || is_wild_any s || is_wild_pre s

    let is_safe s = 
      let re = Str.regexp "[A-Za-z '~' '_' '\'' '@' ][0-9 a-z A-Z '_' '@' '\'' '.' '#']*$" in
      Str.string_match re s 0
    
    let of_string, to_string = 
      let of_t = Hashtbl.create 117 in
      let to_t = Hashtbl.create 117 in
      let bind = fun s sy -> Hashtbl.replace of_t s sy; Hashtbl.replace to_t sy s in
      let f,_  = Misc.mk_string_factory "FIXPOINTSYMBOL_" in
      ((fun s -> 
        if is_wild_fresh s then mk_wild () else
        if is_safe s then s else
           try Hashtbl.find of_t s with Not_found ->
             let sy = f () in
             let _  = bind s sy in sy),
       (fun sy -> try Hashtbl.find to_t sy with Not_found -> sy))
                   
    let to_string = fun s -> s (* if is_safe s then s else "'" ^ s ^ "'" *)

    let suffix = fun s suff -> of_string ((to_string s) ^ suff)

    let print fmt s =
      to_string s |> Format.fprintf fmt "%s" 

    let vvprefix = "VV_"
    let vvsuffix = function
      | Sort.Ptr l -> Sort.loc_to_string l
      | t          -> Sort.to_string_short t



    let is_value_variable = Misc.is_prefix vvprefix
    let value_variable t = vvprefix ^ (vvsuffix t)

    (* DEBUG *)
    let vvprefix = "VV"
    let is_value_variable = (=) vvprefix
    let value_variable _  = vvprefix

    module SMap = Misc.EMap (struct type t = string 
                                    let compare i1 i2 = compare i1 i2 
                                    let print         = print         end)

    module SSet = Misc.ESet (struct type t = string
                                    let compare i1 i2 = compare i1 i2 end)

   (* let sm_length m = 
      SMap.fold (fun _ _ i -> i+1) m 0

    let sm_filter f sm = 
      SMap.fold begin fun x y sm -> 
        if f x y then SMap.add x y sm else sm 
    end sm SMap.empty 

    let sm_to_list sm =
      SMap.fold (fun x y acc -> (x,y)::acc) sm []
    
    let sm_of_list xs = 
      List.fold_left (fun sm (k,v) -> SMap.add k v sm) SMap.empty xs 
   *)

  end

module Constant =
  struct
    type t = Int of int

    let to_string = function
      | Int i -> string_of_int i

    let print fmt s =
      to_string s |> Format.fprintf fmt "%s"
  end
 

type tag = int

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
  | And   of pred list
  | Or    of pred list
  | Not   of pred
  | Imp   of pred * pred
  | Iff   of pred * pred
  | Bexp  of expr
  | Atom  of expr * brel * expr 
  | MAtom of expr * brel list * expr
  | Forall of ((Symbol.t * Sort.t) list) * pred

let list_hash b xs = 
  List.fold_left (fun v (_,id) -> 2*v + id) b xs

module Hashcons (X : sig type t 
                         val sub_equal : t -> t -> bool 
                         val hash : t -> int end) = struct

  module HashStruct = struct
    type t = X.t * int
    let equal (x,_) (y,_) = X.sub_equal x y
    let hash (x,_) = X.hash x
  end

  module Hash = Weak.Make(HashStruct)
  
  let wrap = 
    let tab = Hash.create 251 in
    let ctr = ref 0 in
    fun e -> 
      let res = Hash.merge tab (e, !ctr) in
      let _   = if snd res = !ctr then incr ctr in
      res

  let unwrap (e,_) = e

end

module ExprHashconsStruct = struct
  type t = expr_int
  let sub_equal e1 e2 =
    match e1, e2 with
      | Con c1, Con c2 -> 
          c1 = c2
      | MExp es1, MExp es2 -> 
          es1 = es2
      | Var x1, Var x2 -> 
          x1 = x2
      | App (s1, e1s), App (s2, e2s) ->
	  (s1 = s2) && 
          (try List.for_all2 (==) e1s e2s with _ -> false)
      | Bin (e1, op1, e1'), Bin (e2, op2, e2') ->
          op1 = op2 && e1 == e2 && e1' == e2'
      | MBin (e1, ops1, e1'), MBin (e2, ops2, e2') ->
          ops1 = ops2 && e1 == e2 && e1' == e2'
      | Ite (ip1,te1,ee1), Ite (ip2,te2,ee2) ->
	      ip1 == ip2 && te1 == te2 && ee1 == ee2
      | Fld (s1, e1), Fld (s2, e2) ->
          s1 = s2 && e1 == e2
      | Cst (e1, s1), Cst (e2, s2) ->
          s1 = s2 && e1 == e2
      | _ -> 
          false
  
  let hash = function
    | Con (Constant.Int x) -> 
        x
    | MExp es ->
        list_hash 6 es 
    | Var x -> 
        Hashtbl.hash x
    | App (s, es) -> 
        list_hash ((Hashtbl.hash s) + 1) es 
    | Bin ((_,id1), op, (_,id2)) -> 
        (Hashtbl.hash op) + 1 + (2 * id1) + id2 
    | MBin ((_,id1), op::_ , (_,id2)) -> 
        (Hashtbl.hash op) + 1 + (2 * id1) + id2 
    | Ite ((_,id1), (_,id2), (_,id3)) -> 
        32 + (4 * id1) + (2 * id2) + id3
    | Fld (s, (_,id)) ->
        (Hashtbl.hash s) + 12 + id
    | Cst ((_, id), t) ->
        id + Hashtbl.hash (Sort.to_string t)
    | Bot ->
        0
    | _ -> assertf "pattern error in A.pred hash"

end
  
module ExprHashcons = Hashcons(ExprHashconsStruct)

module PredHashconsStruct = struct
  
  type t = pred_int
  
  let sub_equal p1 p2 =
    match p1, p2 with
      | True, True | False, False -> 
          true
      | And p1s, And p2s  | Or  p1s, Or p2s -> 
          (try List.for_all2 (==) p1s p2s with _ -> false)
      | Not p1, Not p2 -> 
          p1 == p2
      | Imp (p1, p1'), Imp (p2, p2') -> 
          p1 == p2 && p1' == p2'
      | Iff (p1,p1'), Iff (p2,p2') ->
          p1 == p2 && p1' == p2'
      | Bexp e1, Bexp e2 -> 
          e1 == e2
      | Atom (e1, r1, e1'), Atom (e2, r2, e2') ->
          r1 = r2 && e1 == e2 && e1' == e2'
      | MAtom (e1, r1, e1'), MAtom (e2, r2, e2') ->
          r1 = r2 && e1 == e2 && e1' == e2'
      | Forall(q1s,p1), Forall(q2s,p2) -> 
          q1s = q2s && p1 == p2
      | _ -> 
          false
 
 let hash = function
   | True -> 
       0
   | False -> 
       1
   | And ps -> 
       list_hash 2 ps
   | Or ps -> 
       list_hash 3 ps
   | Not (_,id) -> 
       8 + id 
   | Imp ((_,id1), (_,id2)) ->
       20 + (2 * id1) + id2
   | Iff ((_,id1), (_,id2)) ->
       28 + (2 * id1) + id2
   | Bexp (_, id) ->
       32 + id
   | Atom ((_,id1), r, (_,id2)) ->
       36 + (Hashtbl.hash r) + (2 * id1) + id2
   | MAtom ((_,id1), r, (_,id2)) ->
       42 + (Hashtbl.hash r) + (2 * id1) + id2
   | Forall(qs,(_,id)) -> 
       50 + (2 * (Hashtbl.hash qs)) + id
end
  
module PredHashcons = Hashcons(PredHashconsStruct)

let ewr = ExprHashcons.wrap
let euw = ExprHashcons.unwrap
let pwr = PredHashcons.wrap 
let puw = PredHashcons.unwrap

(* Constructors: Expressions *)
let eCon  = fun c  -> ewr  (Con c)
let eMExp = fun es -> ewr  (MExp es)
let eInt  = fun i  -> eCon (Constant.Int i)
let zero  = eInt 0
let one   = eInt 1
let bot  = ewr Bot
let eMod = fun (e, m) -> ewr (Bin (e, Mod, eInt m))
let eModExp = fun (e, m) -> ewr (Bin (e, Mod, m))
let eVar = fun s -> ewr (Var s)
let eApp = fun (s, es) -> ewr (App (s, es))
let eBin = fun (e1, op, e2) -> ewr (Bin (e1, op, e2)) 

let eMBin = fun (e1, ops, e2) -> ewr (MBin (e1, ops, e2)) 
let eIte = fun (ip,te,ee) -> ewr (Ite(ip,te,ee))
let eFld = fun (s,e) -> ewr (Fld (s,e))
let eCst = fun (e,t) -> ewr (Cst (e, t))

let eTim = function 
  | (Con (Constant.Int n1), _), (Con (Constant.Int n2), _) -> 
      ewr (Con (Constant.Int (n1 * n2)))
  | (Con (Constant.Int 1), _), e2 -> 
      e2 
  | (Con (Constant.Int (-1)), _), e2 -> 
      eBin (zero, Minus, e2) 
  | (e1, e2) -> eBin (e1, Times, e2)


let rec conjuncts = function
  | And ps, _ -> Misc.flap conjuncts ps
  | True, _   -> []
  | p         -> [p]


(* Constructors: Predicates *)
let pTrue  = pwr True
let pFalse = pwr False
let pAtom  = fun (e1, r, e2) -> pwr (Atom (e1, r, e2))
let pMAtom = fun (e1, r, e2) -> pwr (MAtom (e1, r, e2))
let pOr    = fun ps -> pwr (Or ps)
let pNot   = fun p  -> pwr (Not p)
let pBexp  = fun e  -> pwr (Bexp e)
let pImp   = fun (p1,p2) -> pwr (Imp (p1,p2))
let pIff   = fun (p1,p2) -> pwr (Iff (p1,p2))
let pForall= fun (qs, p) -> pwr (Forall (qs, p))
let pEqual = fun (e1,e2) -> pAtom (e1, Eq, e2)

let pAnd   = fun ps -> match Misc.flap conjuncts ps with 
                       | []  -> pTrue 
                       | [p] -> p
                       | ps  -> pwr (And (Misc.flap conjuncts ps))



module ExprHash = Hashtbl.Make(struct
  type t = expr
  let equal (_,x) (_,y) = (x = y)
  let hash (_,x) = x
end)

module PredHash = Hashtbl.Make(struct
  type t = pred
  let equal (_,x) (_,y) = (x = y)
  let hash (_,x) = x
end)

let bop_to_string = function 
  | Plus  -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div   -> "/"
  | Mod   -> "mod" 

let brel_to_string = function 
  | Eq -> "="
  | Ne -> "!="
  | Gt -> ">"
  | Ge -> ">="
  | Lt -> "<"
  | Le -> "<="

let print_brel ppf r = 
  F.fprintf ppf "%s" (brel_to_string r)

let print_binding ppf (s,t) = 
  F.fprintf ppf "%a:%a" Symbol.print s Sort.print t

let bind_to_string  (s,t) = 
  Printf.sprintf "%s:%s" (Symbol.to_string s) (Sort.to_string t)

let rec print_expr ppf e = match euw e with
  | Con c -> 
      F.fprintf ppf "%a" Constant.print c 
  | MExp es -> 
      F.fprintf ppf "[%a]" (Misc.pprint_many false " ; " print_expr) es
  | Var s -> 
      F.fprintf ppf "%a" Symbol.print s
  | App (s, es) -> 
      F.fprintf ppf "%a([%a])" 
        Symbol.print s
        (Misc.pprint_many false "; " print_expr) es
  | Bin (e1, op, e2) ->
      F.fprintf ppf "(%a %s %a)" 
        print_expr e1 
        (bop_to_string op) 
        print_expr e2
  | MBin (e1, ops, e2) ->
      F.fprintf ppf "(%a [%s] %a)" 
        print_expr e1 
        (ops |>: bop_to_string |> String.concat " ; ")
        print_expr e2
 
  | Ite(ip,te,ee) -> 
      F.fprintf ppf "(%a ? %a : %a)" 
        print_pred ip 
        print_expr te
        print_expr ee
  | Fld(s, e) -> 
      F.fprintf ppf "%a.%s" print_expr e s 
  | Cst(e,t) ->
      F.fprintf ppf "(%a : %a)" 
        print_expr e 
        Sort.print t
  | Bot ->
      F.fprintf ppf "_|_" 

and print_pred ppf p = match puw p with
  | True -> 
      F.fprintf ppf "true"
  | False -> 
      F.fprintf ppf "false"
  | Bexp (App (s, es), _) ->
      F.fprintf ppf "%a(%a)" Symbol.print s (Misc.pprint_many false ", " print_expr) es
  | Bexp e ->
      F.fprintf ppf "(Bexp %a)" print_expr e
  | Not p -> 
      F.fprintf ppf "(~ (%a))" print_pred p
  | Imp (p1, p2) -> 
      F.fprintf ppf "(%a => %a)" print_pred p1 print_pred p2 
  | Iff (p1, p2) ->
      F.fprintf ppf "(%a <=> %a)" print_pred p1 print_pred p2 
  | And ps -> begin match ps with [] -> F.fprintf ppf "true" | _ ->
      F.fprintf ppf "&& %a" (Misc.pprint_many_brackets true print_pred) ps
    end
  | Or ps -> begin match ps with [] -> F.fprintf ppf "false" | _ -> 
      F.fprintf ppf "|| %a" (Misc.pprint_many_brackets true print_pred) ps
    end

  | Atom (e1, r, e2) ->
      (* F.fprintf ppf "@[(%a %s %a)@]" *)
      F.fprintf ppf "(%a %s %a)"
        print_expr e1 
        (brel_to_string r) 
        print_expr e2
  | MAtom (e1, rs, e2) ->
      F.fprintf ppf "(%a [%a] %a)" 
      (* F.fprintf ppf "@[(%a [%a] %a)@]"  *)
        print_expr e1 
        (Misc.pprint_many false " ; " print_brel) rs
        print_expr e2
  | Forall (qs, p) -> 
      F.fprintf ppf "forall [%a] . %a" 
        (Misc.pprint_many false "; " print_binding) qs
        print_pred p
  
let rec expr_to_string e = 
  match euw e with
  | Con c -> 
      Constant.to_string c
  | MExp es -> 
      Printf.sprintf "[%s]" (es |>: expr_to_string |> String.concat " ; ")
  | Var s -> 
      Symbol.to_string s
  | App (s, es) ->
      Printf.sprintf "%s([%s])" 
        (Symbol.to_string s)
        (es |> List.map expr_to_string |> String.concat "; ")
  | Bin (e1, op, e2) ->
      Printf.sprintf "(%s %s %s)" 
        (expr_to_string e1) (bop_to_string op) (expr_to_string e2)
  | MBin (e1, ops, e2) ->
      Printf.sprintf "(%s [%s] %s)" 
        (expr_to_string e1) 
        (ops |> List.map bop_to_string |> String.concat "; ")
        (expr_to_string e2)
  | Ite(ip,te,ee) -> 
      Printf.sprintf "(%s ? %s : %s)" 
        (pred_to_string ip) (expr_to_string te) (expr_to_string ee)
  | Fld(s,e) -> 
      Printf.sprintf "%s.%s" (expr_to_string e) s 
  | Cst(e,t) ->
      Printf.sprintf "(%s : %s)" (expr_to_string e) (Sort.to_string t)
  | Bot ->
      Printf.sprintf "_|_" 


and pred_to_string p = 
  match puw p with
    | True -> 
        "true"
    | False -> 
        "false"
    | Bexp e ->
        Printf.sprintf "(Bexp %s)" (expr_to_string e)
    | Not p -> 
        Printf.sprintf "(~ (%s))" (pred_to_string p) 
    | Imp (p1, p2) -> 
        Printf.sprintf "(%s => %s)" (pred_to_string p1) (pred_to_string p2)
    | Iff (p1, p2) ->
        Printf.sprintf "(%s <=> %s)" (pred_to_string p1) (pred_to_string p2)
    | And ps -> 
        Printf.sprintf "&& [%s]" (List.map pred_to_string ps |> String.concat " ; ")
    | Or ps -> 
        Printf.sprintf "|| [%s]" (List.map pred_to_string ps |> String.concat ";")
    | Atom (e1, r, e2) ->
        Printf.sprintf "(%s %s %s)" 
        (expr_to_string e1) (brel_to_string r) (expr_to_string e2)
    | MAtom (e1, rs, e2) ->
        Printf.sprintf "(%s [%s] %s)" 
        (expr_to_string e1)
        (List.map brel_to_string rs |> String.concat " ; ") 
        (expr_to_string e2)
    | Forall (qs,p) -> 
        Printf.sprintf "forall [%s] . %s" 
        (List.map bind_to_string qs |> String.concat "; ") (pred_to_string p)

let rec pred_map hp he fp fe p =
  let rec pm p =
    try PredHash.find hp p with Not_found -> begin
      let p' = 
        match puw p with
        | True | False as p1 -> 
            p1
        | And ps -> 
            And (List.map pm ps)  
        | Or ps -> 
            Or (List.map pm ps)  
        | Not p -> 
            Not (pm p) 
        | Imp (p1, p2) -> 
            Imp (pm p1, pm p2)
        | Iff (p1, p2) ->
            Iff (pm p1, pm p2)
        | Bexp e ->
            Bexp (expr_map hp he fp fe e) 
        | Atom (e1, r, e2) ->
            Atom (expr_map hp he fp fe e1, r, expr_map hp he fp fe e2)
        | MAtom (e1, rs, e2) ->
            MAtom (expr_map hp he fp fe e1, rs, expr_map hp he fp fe e2)
        | Forall (qs, p) ->
            Forall (qs, pm p) in
      let rv = fp (pwr p') in
      let _  = PredHash.add hp p rv in 
      rv
    end in pm p 

and expr_map hp he fp fe e =
  let rec em e =
    try ExprHash.find he e with Not_found -> begin
      let e' = 
        match euw e with
        | Con _ | Var _ | Bot as e1 -> 
            e1
        | MExp es ->
            MExp (List.map em es) 
        | App (f, es) ->
            App (f, List.map em es)
        | Bin (e1, op, e2) ->
            Bin (em e1, op, em e2)
        | MBin (e1, ops, e2) ->
            MBin (em e1, ops, em e2)
        | Ite (ip, te, ee) ->
            Ite (pred_map hp he fp fe ip, em te, em ee) 
        | Fld (s, e1) -> 
            Fld (s, em e1) 
        | Cst (e1, t) -> 
            Cst (em e1, t) 
      in
      let rv = fe (ewr e') in
      let _  = ExprHash.add he e rv in
      rv
    end in em e

let rec pred_iter fp fe pw =
  begin match puw pw with
    | True | False -> ()
    | Bexp e -> expr_iter fp fe e
    | Not p -> pred_iter fp fe p
    | Imp (p1, p2) -> pred_iter fp fe p1; pred_iter fp fe p2
    | Iff (p1, p2) -> pred_iter fp fe p1; pred_iter fp fe p2
    | And ps | Or ps -> List.iter (pred_iter fp fe) ps
    | Atom (e1, _, e2) -> expr_iter fp fe e1; expr_iter fp fe e2
    | MAtom (e1, _, e2) -> expr_iter fp fe e1; expr_iter fp fe e2
    | Forall (_, p) -> pred_iter fp fe p (* pmr: looks wrong, but so does pred_map *)
  end;
  fp pw

and expr_iter fp fe ew =
  begin match puw ew with
    | Con _ | Var _ | Bot -> 
        ()
    | MExp es ->
        List.iter (expr_iter fp fe) es
    | App (_, es)  -> 
        List.iter (expr_iter fp fe) es
    | Bin (e1, _, e2)  -> 
        expr_iter fp fe e1; expr_iter fp fe e2
    | MBin (e1, _, e2)  -> 
        expr_iter fp fe e1; expr_iter fp fe e2
    | Ite (ip, te, ee) -> 
        pred_iter fp fe ip; expr_iter fp fe te; expr_iter fp fe ee
    | Fld (_, e1) | Cst (e1, _) -> 
        expr_iter fp fe e1
  end;
  fe ew

let esub x e = function
  | (Var y), _ when x = y -> e
  | _ as e1 -> e1 

let expr_subst hp he e x e' =
  expr_map hp he id (esub x e') e 

let pred_subst hp he p x e' =
  pred_map hp he id (esub x e') p 

module Expression = 
  struct
      
    module Hash   = ExprHash 
      
    let to_string = expr_to_string

    (* let print     = fun fmt e -> Format.pp_print_string fmt (to_string e)
     *)
    let print = print_expr
    
    let show      = print Format.std_formatter

    let map fp fe e =
      let hp = PredHash.create 251 in
      let he = ExprHash.create 251 in 
      expr_map hp he fp fe e 

    let iter fp fe e =
      expr_iter fp fe e

    let subst e x e' =
      map id (esub x e') e

    let substs e xes =
      map id (fun e -> List.fold_left (esub |> Misc.uncurry |> Misc.flip) e xes) e

    let support e =
      let xs = ref Symbol.SSet.empty in
      iter un begin function 
        | (Var x), _ 
        | (App (x,_)),_ -> xs := Symbol.SSet.add x !xs
        | _               -> ()
      end e;
      Symbol.SSet.elements !xs |> List.sort compare

    let unwrap = euw

    let has_bot p =
      let r = ref false in
      iter un begin function 
        | Bot, _ -> r := true
        | _      -> ()
      end p; 
      !r

  end
    
module Predicate = struct
  module Hash = PredHash 
	
  let to_string = pred_to_string
  let print     = print_pred
  let show      = print Format.std_formatter
			
  let map fp fe p =
	let hp = PredHash.create 251 in
	let he = ExprHash.create 251 in 
    pred_map hp he fp fe p
	
  let iter fp fe p =
    pred_iter fp fe p

  let subst p x e' =
    map id (esub x e') p

  let substs p xes =
    map id (fun e -> List.fold_left (esub |> Misc.uncurry |> Misc.flip) e xes) p

  let support p =
    let xs = ref Symbol.SSet.empty in
    iter un begin function 
      | (Var x), _ 
      | (App (x,_)),_ -> xs := Symbol.SSet.add x !xs;
      | _               -> ()
    end p; 
    Symbol.SSet.elements !xs |> List.sort compare

  (*
  let size p =
	let c = ref 0           in
    let f = fun _ -> incr c in
    let _ = iter f f p      in 
    !c

  let size p =
	let c = ref 0                    in
    let _ = iter (fun _ -> incr c) p in 
    !c
  *)
  
  let unwrap = puw

  let is_contra = 
    let t = PredHash.create 17 in
    let _ = [pFalse; pNot pTrue; pAtom (zero, Eq, one); pAtom (one, Eq, zero)]
            |> List.iter (fun p-> PredHash.replace t p ()) in 
    fun p -> PredHash.mem t p 
   

  let rec is_tauto  = function
    | Atom(e1, Eq, e2), _ -> snd e1 == snd e2
    | Imp (p1, p2), _     -> snd p1 == snd p2
    | And ps, _           -> List.for_all is_tauto ps
    | Or  ps, _           -> List.exists is_tauto ps
    | True, _             -> true
    | _                   -> false

  let has_bot p =
    let r = ref false in
    iter un begin function 
      | Bot, _ -> r := true
      | _      -> ()
    end p; 
    !r

  end

let print_stats _ = 
  Printf.printf "Ast Stats. [none] \n"


(********************************************************************************)
(************************** Rationalizing Division ******************************)
(********************************************************************************)

let expr_isdiv = function
  | Bin (_, Div, _), _ -> true
  | _                  -> false

let pull_divisor = function 
  | Bin (_, Div, (Con (Constant.Int i),_)), _ -> i 
  | _ -> 1

let calc_cm e1 e2 =
    pull_divisor e1 * pull_divisor e2 

let rec apply_mult m = function 
  | Bin (e, Div,  (Con (Constant.Int d),_)), _ ->
      let _   = assert ((m/d) * d = m) in
      eTim ((eCon (Constant.Int (m/d))), e)  
  | Bin (e1, op, e2), _ ->
      eBin (apply_mult m e1, op, apply_mult m e2)
  | Con (Constant.Int i), _ -> 
      eCon (Constant.Int (i*m))
  | e -> 
      eTim (eCon (Constant.Int m), e)

let rec pred_isdiv = function 
  | True,_ | False,_ -> 
      false
  | And ps,_ | Or ps,_ -> 
      List.exists pred_isdiv ps
  | Not p, _ | Forall (_, p), _ -> 
      pred_isdiv p
  | Imp (p1, p2), _ ->
      pred_isdiv p1 || pred_isdiv p2
  | Iff (p1, p2), _ ->
      pred_isdiv p1 || pred_isdiv p2
  | Bexp e, _ ->
      expr_isdiv e
  | Atom (e1, _, e2), _ -> 
      expr_isdiv e1 || expr_isdiv e2
  | _ -> failwith "Unexpected: pred_isdiv"

let bound m e e1 e2 =
  pAnd [pAtom (apply_mult m e, Gt, apply_mult m e2);
        pAtom(apply_mult m e, Le, apply_mult m e1)] 

let rec fixdiv = function
  | p when not (pred_isdiv p) -> 
      p
  | Atom ((Var _,_) as e, Eq, e1), _ | Atom ((Con _, _) as e, Eq, e1), _ ->
      bound (calc_cm e e1) e e1 (eBin (e1, Minus, one))
  | And ps, _ ->
      pAnd (List.map fixdiv ps) 
  | Or ps, _ ->
      pOr (List.map fixdiv ps)
  | Imp (p1, p2), _ ->
      pImp (fixdiv p1, fixdiv p2)
  | Iff (p1, p2), _ ->
      pIff (fixdiv p1, fixdiv p2)
  | Not p, _ -> 
      pNot (fixdiv p) 
  | p -> p

(***************************************************************************)
(************* Type Checking Expressions and Predicates ********************)
(***************************************************************************)

let sortcheck_sym f s = f s
  (* try Some (f s)  with _ -> None *)

let sortcheck_loc f = function
  | Sort.Loc s  -> sortcheck_sym f (Symbol.of_string s)
  | Sort.Lvar _ -> None
  | Sort.LFun   -> None

let rec sortcheck_expr f e = 
  match euw e with
  | Bot   -> 
      None
  | Con _ -> 
      Some Sort.Int 
  | Var s ->
      sortcheck_sym f s
  | Bin (e1, op, e2) -> 
      sortcheck_op f (e1, op, e2)
  | Ite (p, e1, e2) -> 
      if sortcheck_pred f p then 
        match Misc.map_pair (sortcheck_expr f) (e1, e2) with
        | (Some t1, Some t2) when t1 = t2 -> Some t1 
        | _ -> None
      else None
  
  | Cst (e1, t) ->
      begin match euw e1 with
        | App (uf, es) -> sortcheck_app f (Some t) uf es
        | _            ->
            match sortcheck_expr f e1 with
              | Some t1 when Sort.compat t t1 -> Some t
              | _                             -> None 
      end

  | App (uf, es) ->
      sortcheck_app f None uf es
    
  | _ -> assertf "Ast.sortcheck_expr: unhandled expr = %s" (Expression.to_string e)

(* TODO: OMG! 5 levels of matching!!!!! *)
and sortcheck_app_sub f so_expected uf es =
  let yikes uf = F.printf "sortcheck_app_sub: unknown sym = %s \n" (Symbol.to_string uf) in
  sortcheck_sym f uf
  |> function None -> (yikes uf; None) | Some t -> 
       Sort.func_of_t t 
       |> function None -> None | Some (tyArity, i_ts, o_t) -> 
              let _  = asserts (List.length es = List.length i_ts) 
                         "ERROR: uf arg-arity error: uf=%s" uf in
              let e_ts = es |> List.map (sortcheck_expr f) |> Misc.map_partial id in
                if List.length e_ts <> List.length i_ts then 
                  None 
                else
                  match Sort.unify i_ts e_ts with
                    | None   -> None
                    | Some s ->
                        let t = Sort.apply s o_t in
                          match so_expected with
                            | None    -> Some (s, t)
                            | Some t' ->
                                match Sort.unifyWith s [t] [t'] with
                                  | None    -> None
                                  | Some s' -> Some (s', Sort.apply s' t)

and sortcheck_app f so_expected uf es = 
  sortcheck_app_sub f so_expected uf es 
  |> Misc.maybe_map snd 
  (* >> begin function 
       | Some t -> Format.printf "sortcheck_app: e = %s , t = %s \n"
                     (expr_to_string (eApp (uf, es))) (Sort.to_string t)
       | None   -> Format.printf "sortcheck_app: e = %s FAILS\n"
                     (expr_to_string (eApp (uf, es)))
     end
  *)



and sortcheck_op f (e1, op, e2) = 
  match Misc.map_pair (sortcheck_expr f) (e1, e2) with
  | (Some Sort.Int, Some Sort.Int) 
  -> Some Sort.Int
  
  (* only allow when language is Haskell *)
  | (Some (Sort.Ptr l), Some (Sort.Ptr l')) 
  when (l = l' && sortcheck_loc f l = Some Sort.Num)
 -> Some (Sort.Ptr l)
 
  (* only allow when language is C *)
  | (Some (Sort.Ptr s), Some Sort.Int) 
  | (Some Sort.Int, Some (Sort.Ptr s)) 
  -> Some (Sort.Ptr s)

  (* only allow when language is C *)
  | (Some (Sort.Ptr s), Some (Sort.Ptr s')) 
  when op = Minus && s = s'
  -> Some Sort.Int

  | _ -> None


and sortcheck_rel f (e1, r, e2) =
  let t1o, t2o = (e1,e2) |> Misc.map_pair (sortcheck_expr f) in
  match r, t1o, t2o with
  | _, Some (Sort.Ptr _) , Some (Sort.Ptr Sort.LFun)
  | _, Some (Sort.Ptr Sort.LFun), Some (Sort.Ptr _)
    -> true
  | _ , Some Sort.Int,     Some (Sort.Ptr l)
  | _ , Some (Sort.Ptr l), Some Sort.Int
    -> (sortcheck_loc f l = Some Sort.Num)
  | Eq, Some t1, Some t2
  | Ne, Some t1, Some t2
    -> t1 = t2
  | _ , Some t1, Some t2
    -> t1 = t2 && t1 != Sort.Bool
  | _ -> false

and sortcheck_pred f p =
  match puw p with
    | True  
    | False -> 
        true 
    | Bexp e ->
        sortcheck_expr f e = Some Sort.Bool 
    | Not p -> 
        sortcheck_pred f p
    | Imp (p1, p2) | Iff (p1, p2) -> 
        List.for_all (sortcheck_pred f) [p1; p2]
    | And ps  
    | Or ps ->
        List.for_all (sortcheck_pred f) ps
    
    | Atom ((Con (Constant.Int(0)),_), _, e) 
    | Atom (e, _, (Con (Constant.Int(0)),_)) 
      when not (!Constants.strictsortcheck)
      -> not (None = sortcheck_expr f e)
    
    | Atom ((Var x, _) , Eq, (App (uf, es), _))
    | Atom ((App (uf, es), _), Eq, (Var x, _))
      -> begin match sortcheck_sym f x with 
         | None    -> false 
         | Some tx -> not (None = sortcheck_app f (Some tx) uf es)
         end

    | Atom (e1, r, e2) ->
        sortcheck_rel f (e1, r, e2)
    | Forall (qs,p) ->
        (* let f' = fun x -> try List.assoc x qs with _ -> f x in *)
        let f' = fun x -> match Misc.list_assoc_maybe x qs with None -> f x | y -> y
        in sortcheck_pred f' p
    | _ -> failwith "Unexpected: sortcheck_pred"

(* and sortcheck_pred f p =
  sortcheck_pred' f p
  >> (fun b -> if not b then F.eprintf "WARNING: Malformed Lhs Pred (%a)\n" Predicate.print p) 
 *)

let uf_arity f uf =  
  match sortcheck_sym f uf with None -> None | Some t -> 
    match Sort.func_of_t t with None -> None | Some (i,_,_) -> 
      Some i
 
(* API *)
let sortcheck_app f t uf es = 
  match uf_arity f uf, sortcheck_app_sub f t uf es with 
    | (Some n , Some (s, t)) -> 
        if Sort.check_arity n s then Some (s, t) else
           assertf "Ast.sortcheck_app: type args not fully instantiated %s" 
             (expr_to_string (eApp (uf, es)))
    | _ -> None

(*
let sortcheck_pred f p = 
  sortcheck_pred f p
  >> (fun b -> ignore <| F.printf "sortcheck_pred: p = %a, res = %b\n"
  Predicate.print p b)
*)

(***************************************************************************)
(************* Simplifying Expressions and Predicates **********************)
(***************************************************************************)

let pred_of_bool = function true -> pTrue | false -> pFalse

let rec remove_bot pol ((p, _) as pred) =
  match p with
  | Not p  -> 
      pNot (remove_bot (not pol) p)
  | Imp (p, q) ->
      pImp (remove_bot (not pol) p, remove_bot pol q)
  | Forall (qs, p) ->
      pForall (qs, remove_bot pol p)
  | And ps ->
      ps |> List.map (remove_bot pol) |> pAnd
  | Or ps -> 
      ps |> List.map (remove_bot pol) |> pOr
  | Bexp e when Expression.has_bot e ->
      pred_of_bool pol
  | Atom (e1, _, e2) when Expression.has_bot e1 || Expression.has_bot e2 -> 
      pred_of_bool pol
  | _ -> 
      pred

let remove_bot p = 
  if Predicate.has_bot p 
  then remove_bot true p 
  else p

let symm_brel = function
  | Eq -> Eq 
  | Ne -> Ne 
  | Gt -> Lt
  | Ge -> Le
  | Lt -> Gt
  | Le -> Ge


let neg_brel = function 
  | Eq -> Ne
  | Ne -> Eq
  | Gt -> Le
  | Ge -> Lt
  | Lt -> Ge
  | Le -> Gt

let rec push_neg ?(neg=false) ((p, _) as pred) =
  match p with
    | True   -> 
        if neg then pFalse else pred
    | False  -> 
        if neg then pTrue else pred
    | Bexp _ -> 
        if neg then pNot pred else pred
    | Not p  -> 
        push_neg ~neg:(not neg) p
    | Imp (p, q) -> 
	if neg then pAnd [push_neg p; push_neg ~neg:true q]
	else pImp (push_neg p, push_neg q)
    | Iff (p, q) ->
        if neg then pIff (p, push_neg ~neg:true q)
        else pIff (push_neg p, push_neg q)
    | Forall (qs, p) -> 
	let pred' = pForall (qs, push_neg ~neg:false p) in
	if neg then pNot pred' else pred'
    | And ps -> 
        List.map (push_neg ~neg:neg) ps 
        |> if neg then pOr else pAnd
    | Or ps -> 
        List.map (push_neg ~neg:neg) ps 
        |> if neg then pAnd else pOr
    | Atom (e1, brel, e2) -> 
        if neg then pAtom (e1, neg_brel brel, e2) else pred
    | _ -> failwith "Unexpected: push_neg"

(* Andrey: TODO flatten nested conjunctions/disjunctions *)
let rec simplify_pred ((p, _) as pred) =
  match p with
    | Not p -> pNot (simplify_pred p)
    | Imp (p, q) -> pImp (simplify_pred p, simplify_pred q) 
    | Forall (qs, p) -> pForall (qs, simplify_pred p)
    | And ps -> ps |> List.map simplify_pred 
                   |> List.filter (not <.> Predicate.is_tauto) 
                   |> (function | []  -> pTrue
                                | [p] -> p
                                | _ when List.exists Predicate.is_contra ps -> pFalse
                                | _   -> pAnd ps)
    | Or ps -> ps |> List.map simplify_pred 
                  |> List.filter (not <.> Predicate.is_contra)
                  |> (function []  -> pFalse
                             | [p] -> p
                             | ps when List.exists Predicate.is_tauto ps -> pTrue
                             | ps  -> pOr ps)
    | _ -> pred

(**************************************************************************)
(*************************** Substitutions ********************************)
(**************************************************************************)

module Subst = struct

  type t = expr Symbol.SMap.t
 
  let valid xes = 
    xes |> List.split 
        |> Misc.app_snd (Misc.flap Expression.support)
        |> Misc.uncurry Misc.disjoint
            
    
  let extend s (x, e) =
    let s = Symbol.SMap.map (esub x e) s in
      if Symbol.SMap.mem x s then
        s
      else
        match e with
        | Var x', _ when x = x' -> s
        | _                     -> Symbol.SMap.add x e s

  let empty     = Symbol.SMap.empty
  let is_empty  = Symbol.SMap.is_empty
  let to_list   = Symbol.SMap.to_list   
  let apply     = Misc.flip Symbol.SMap.maybe_find
  let of_list   = fun xes -> List.fold_left extend empty xes
  let simultaneous_of_list = Symbol.SMap.of_list
  let compose s t = 
    let s' = Symbol.SMap.fold (fun x e s -> Symbol.SMap.map (esub x e) s) t s
    in Symbol.SMap.fold (fun x e s -> if Symbol.SMap.mem x s
                                         then s else Symbol.SMap.add x e s)
                        t s'
  let print_sub = fun ppf (x,e) -> F.fprintf ppf "[%a:=%a]" Symbol.print x Expression.print e
  let print     = fun ppf -> to_list <+> F.fprintf ppf "%a" (Misc.pprint_many false "" print_sub)
      
(* fun s1 s2 -> Symbol.SMap.fold (fun x e s -> extend s (x, e)) s2 s1 *)
(*   let apply     = Misc.flip Symbol.SMap.maybe_find *)

end


(**************************************************************************)
(******************* Horn Clauses: Parsing ARMC files *********************)
(**************************************************************************)

module Horn = struct
  
  type pr = string * string list
  type gd = C of pred | K of pr
  type t  = pr * gd list 

  let print_pr ppf (x, xs) = 
    Format.fprintf ppf "%s(%s)" x (String.concat "," xs) 
    
  let print_gd ppf = function 
    | C p -> Predicate.print ppf p
    | K x -> print_pr ppf x 

  let print ppf (hd, gds) = 
    Format.fprintf ppf "%a :- %a." 
      print_pr hd 
      (Misc.pprint_many false "," print_gd) gds

  let support_pr = snd 
  let support_gd = function K pr -> support_pr pr | C p  -> p |> Predicate.support |> List.map Symbol.to_string 
  let support    = fun (hd, gds) -> (support_pr hd) ++ (Misc.flap support_gd gds)
end

(* API *)
let simplify_pred = remove_bot <+> simplify_pred


let esub_su su e = match e with 
  | ((Var y), _) -> Misc.maybe_default (Subst.apply su y) e
  | _            -> e

(* ORIG 
   let substs_pred   = fun p su -> su |> Subst.to_list |> Predicate.substs p |> simplify_pred
*)

let substs_pred p su = Predicate.map  id (esub_su su) p
let substs_expr e su = Expression.map id (esub_su su) e

(****************************************************************************)
(******************** Unification of Predicates *****************************)
(****************************************************************************)


exception DoesNotUnify 

let rec pUnify (p1, p2) = 
  let res = 
    match p1, p2 with
  | (Atom (e1, r1, e1'), _), (Atom (e2, r2, e2'), _) when r1 = r2 ->
      let s1       = eUnify (e1, e2) in
      let e1', e2' = Misc.map_pair ((Misc.flip Expression.substs) s1) (e1', e2') in
      let s2       = eUnify (e1', e2') in
      s1 ++ s2
  | (Bexp e1, _), (Bexp e2, _) ->
      eUnify (e1, e2)
  | (Not p1, _), (Not p2, _) ->
      pUnify (p1, p2)
  | (Imp (p1, p1'), _), (Imp (p2, p2'), _) ->
      psUnify ([p1; p1'], [p2; p2'])
  
  | (And p1s, _), (And p2s, _) 
  | (Or p1s, _), (Or p2s, _) 
    when List.length p1s = List.length p2s ->
      psUnify (p1s, p2s)
  | _, _ -> raise DoesNotUnify
  in
  let _ = if mydebug then 
          (Format.printf "pUnify: p1 is %a, p2 is %a, subst = %a \n" 
          Predicate.print p1 Predicate.print p2 Subst.print (Subst.of_list res)) in
  res

and psUnify (p1s, p2s) =
  let _ = asserts (List.length p1s = List.length p2s) "psUnify" in
  List.fold_left2 begin fun s p1 p2 ->
    (p1, p2) 
    |> Misc.map_pair (fun p -> Predicate.substs p s)
    |> pUnify
    |> (fun s' -> s' ++ s)
  end [] p1s p2s

and eUnify = function
  | (Con c1, _), (Con c2, _) when c1 = c2 ->
      []
  | (Var x1, _), (Var x2, _) when x1 = x2 ->
      []
  | (Bin (e1, op1, e1'),_), (Bin (e2, op2, e2'), _) when op1 = op2 ->
      esUnify ([e1; e1'], [e2; e2'])
  | (Ite (p1, e1, e1'),_), (Ite (p2, e2, e2'), _) ->
      let s = pUnify (p1, p2) in
      let [e1; e1'; e2; e2'] = List.map ((Misc.flip Expression.substs) s) [e1; e1'; e2; e2'] in
      esUnify ([e1; e1'], [e2; e2'])
  | (Cst (e1, t1),_), (Cst (e2, t2),_) when t1 = t2 ->
      eUnify (e1, e2)
  | (App (uf1, e1s), _), (App (uf2, e2s),_) when uf1 = uf2 ->
      esUnify (e1s, e2s)
  | e, (Var x, _) | (Var x, _), e when Symbol.is_wild x ->
      [(x, e)]
  | _, _ -> raise DoesNotUnify 

and esUnify (e1s, e2s) =
  let _ = asserts (List.length e1s = List.length e2s) "esUnify" in
  List.fold_left2 begin fun s e1 e2 ->
    (e1, e2) 
    |> Misc.map_pair (fun e -> Expression.substs e s)
    |> eUnify
    |> (fun s' -> s' ++ s)
  end [] e1s e2s

(* API *)
let unify_pred p1 p2 = try pUnify (p1, p2) |> Subst.of_list |> some with DoesNotUnify -> None 
let into_of_expr = function Con (Constant.Int i), _  -> Some i | _ -> None

let symm_pred = function 
  | Atom (e1, r, e2), _ -> pAtom (e2, symm_brel r, e1)
  | p                   -> p

(* {{{
let rec expr_subst hp he e x e' =
  let rec esub e =
    try ExprHash.find he e with Not_found -> begin
      let rv = 
        match euw e with
        | Var y when x = y ->
            e' 
        | Con _ | Var _ -> 
            e
        | App (s, es) ->
            App (s, List.map esub es) |> ewr
        | Bin (e1, op, e2) ->
            Bin (esub e1, op, esub e2) |> ewr
        | Ite (ip, te, ee) ->
            Ite (pred_subst hp he ip x e', esub te, esub ee) |> ewr
        | Fld (s, e1) ->
            Fld (s, esub e1) |> ewr in
      let _  = ExprHash.add he e rv in
      rv 
    end in esub e

and pred_subst hp he e x e' =
  let rec s e =
    try PredHash.find h e with
	Not_found -> (let foo = s1 e in PredHash.add h e foo; foo)
  and s1 e =
    match puw e with
	True -> e
      | False -> e
      | And plist -> pwr (And(List.map s plist))
      | Or plist -> pwr (Or(List.map s plist))
      | Not p -> pwr (Not(s p))
      | Implies (p1, p2) -> pwr (Implies (s p1, s p2))
      | Equality (x,y) -> pwr (Equality(expr_subst h he x v vv,expr_subst h he y v vv))
      | Atom (_) -> e
      | Leq(x,y) -> pwr (Leq(expr_subst h he x v vv, expr_subst h he y v vv))
  in s e
}}} *)  
(** {{{
      let rec support pred =
        let h = Hash.create 251 in
        let eh = Expression.Hash.create 251 in
        let sh = Hashtbl.create 251 in
        let res = ref [] in
        let add s = if not(Hashtbl.mem sh s) then Hashtbl.add sh s (); res := s :: !res in

        let se exp =
          let rec s exp =
            try Expression.Hash.find eh exp with
                Not_found -> Expression.Hash.add eh exp (); s1 exp
          and s1 exp =
            match euw exp with
                Constant(_) -> ()
              | Application (func, args) -> 
                  add func; List.iter s args
              | Variable(sym) -> add sym
              | Sum(args) -> List.iter s args
              | Coeff(c,t) -> s t
              | Ite _ -> failwith "ite not supported"
          in s exp in
          
        let rec s exp =
          try Hash.find h exp with
              Not_found -> Hash.add h exp (); s1 exp
        and s1 pred =
          match puw pred with
              True -> ()
            | False -> ()
            | And plist -> List.iter s plist
            | Or plist -> List.iter s plist
            | Not p -> s p
            | Implies (p1, p2) -> s p1; s p2
            | Equality (x,y) -> se x; se y
            | Leq (x,y) -> se x; se y
            | Atom (s) -> ()
        in s pred; List.rev !res
        
      let h = PredHash.create 251 in
        let rec ip p =
          let _ = f p in
          if not (PredHash.mem h p) then begin
            let _ = PredHash.add h p () in
            match puw p with
            | And ps | Or ps -> 
                List.iter ip plist
            | Not p  | Forall (_,p) -> 
                ip p 
            | Imp (p1, p2) -> 
                ip p1; ip p2
            | _ -> ()
          end in
        ip p 
   }}} *)
(* {{{
  
      (* Translate predicate to a satisfiability-equivalent predicate without Ite *)
      
      let temp_ctr = ref 0
      let new_temp () =
	let n = "$$$" ^ (string_of_int !temp_ctr) in
	  (temp_ctr := !temp_ctr + 1; n)
	  
      let elim_ite sp =
	let cnsts = ref [] in
	let he = Expression.Hash.create 251 in
	let hp = Hash.create 251 in
	let rec te e =
	  try Expression.Hash.find he e
	  with Not_found -> (let foo = te1 e in Expression.Hash.add he e foo; foo)
	and te1 e =
	  match euw e with
	      Constant(c) -> e
	    | Application (func, args) -> 
		ewr (Application (func, List.map te args))
	    | Variable(v) -> ewr (Variable(v))
	    | Sum(args) -> ewr (Sum(List.map te args))
	    | Coeff(c,t) -> ewr (Coeff(c,te t))
	    | Ite(si,st,se) ->
		let temp = ewr (Variable(new_temp())) in
		let i = tp si in
		let tv = te st and ev = te se in
		  begin
		    cnsts := pwr (Or [pwr (Not i); pwr (Equality(temp,(tv)))]) :: (!cnsts);
		    cnsts := pwr (Or [i; pwr (Equality(temp,(ev)))]) :: (!cnsts);
		    temp
		  end
	and tp p = 
	  try Hash.find hp p
	  with Not_found -> (let foo = tp1 p in Hash.add hp p foo; foo)
	and tp1 p =
	  match puw p with
	      True -> p
	    | False -> p
	    | And plist -> pwr (And (List.map tp plist))
	    | Or plist -> pwr (Or (List.map tp plist))
	    | Not p -> pwr (Not (tp p))
	    | Implies (p1, p2) -> pwr (Implies((tp p1),(tp p2)))
	    | Equality (x,y) -> pwr(Equality((te x),(te y)))
	    | Leq (x,y) -> pwr(Leq((te x),(te y)))
	    | Atom (s) -> p
	in
	let foo = tp sp in
	  pwr (And(foo :: !cnsts))
    }}} *)
