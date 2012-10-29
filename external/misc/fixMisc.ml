(*
 * Copyright ? 1990-2007 The Regents of the University of California. All rights reserved. 
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

(* $Id: misc.ml,v 1.14 2006/09/26 01:47:01 jhala Exp $
 *
 * This file is part of the SIMPLE Project.
 *)

(**
 * This module provides some miscellaneous useful helper functions.
 *)

module Ops = struct

  type ('a, 'b) either = Left of 'a | Right of 'b

  let (>|) _ x = x

  let (|>) x f = f x

  let (<|) f x = f x

  let (>>) x f = f x; x

  let (|>>) xo f = match xo with None -> None | Some x -> f x

  let (|>:) xs f = List.map f xs

  let (=+) x n = let v = !x in (x := v + n; v)

  let (+=) x n = x := !x + n; !x

  let (++) = List.rev_append

  let (+++)= fun (x1s, y1s) (x2s, y2s) -> (x1s ++ x2s, y1s ++ y2s)

  let id = fun x -> x

  let un = fun x -> ()

  let const x = fun _ -> x

  let (<.>) f g  = fun x -> x |> g |> f

  let (<+>) f g  = fun x -> x |> f |> g 

  let (<?>) b f  = fun x -> if b then f x else x

  let wwhen b f  = fun x -> if b then f x 

  let (<*>) f g  = fun x -> (f x, g x)
  
  let (<**>) f g = fun (x, y) -> (f x, g y)

  let (<&&>) f g = fun x -> f x && g x

  let failure fmt = Printf.ksprintf failwith fmt

  let foreach xs f = List.map f xs

  let asserts p fmt =
    Printf.ksprintf (fun x -> if not p then failwith x) fmt

let asserti = asserts
  (*
let asserti p fmt = 
  Printf.ksprintf (fun x -> if not p then (print_string (x^"\n"); ignore(0/0)) else ()) fmt
*)

let assertf fmt =
  Printf.ksprintf failwith fmt

let halt _ =
  assert false

let fst3 (x,_,_) = x
let snd3 (_,x,_) = x
let thd3 (_,_,x) = x

let fst4 (x, _, _, _) = x
let snd4 (_, x, _, _) = x
let thd4 (_, _, x, _) = x
let fth4 (_, _, _, x) = x

let withfst3 (_,y,z) x = (x,y,z)
let withsnd3 (x,_,z) y = (x,y,z)
let withthd3 (x,y,_) z = (x,y,z)

let print_now s = 
  print_string s;
  flush stdout

let print_now_error msg =
  prerr_string msg;
  flush stderr




let some = fun x -> Some x

end

open Ops

let maybe_fold f b xs = 
  let fo = fun bo x -> match bo with Some b -> f b x | _ -> None in
  List.fold_left fo (Some b) xs

let maybe_map f = function Some x -> Some (f x) | None -> None

let maybe_iter f = function Some x -> f x | None -> ()

let maybe = function Some x -> x | _ -> assertf "maybe called with None"

let maybe_apply f xo v = match xo with Some x -> f x v | None -> v

let maybe_default xo y = match xo with Some x -> x | None -> y

let maybe_string f = function Some x -> "Some " ^ (f x) | None -> "None"

let rec maybe_chain x d = function 
  | f::fs -> (match f x with 
              | Some y -> y 
              | None -> maybe_chain x d fs)
  | []    -> d





let trace s f x =
  let _ = print_now <| Printf.sprintf "BEGIN: %s \n" s in
  let r = f x in
  let _ = print_now <| Printf.sprintf "END: %s \n" s   in
  r

(* ORIG
let rec pprint_many_box s f ppf = function
  | []     -> ()
  | x::[]  -> Format.fprintf ppf "%a" f x
  | x::xs' -> (Format.fprintf ppf "%a%s@\n" f x s; pprint_many_box s f ppf xs')
*)
let rec pprint_many_prefix sep base f ppf = function
  | x::xs -> Format.fprintf ppf "(%s %a %a)" 
               sep f x (pprint_many_prefix sep base f) xs
  | []    -> Format.fprintf ppf "%a" f base


let rec pprint_many_box brk s f ppf = function
  | []              -> ()
  | [x]             -> Format.fprintf ppf "%a" f x
  | x::xs' when brk -> Format.fprintf ppf "%a@\n%s" f x s; 
                       pprint_many_box brk s f ppf xs'
  | x::xs'          -> Format.fprintf ppf "%a@,%s" f x s;
                       pprint_many_box brk s f ppf xs'

let pprint_many_box brk l s r f ppf = function
  | []     -> Format.fprintf ppf "[]"
  | xs     -> Format.fprintf ppf "@[%s%a%s@]" l (pprint_many_box brk s f) xs r

let pprint_many_brackets brk f ppf x = 
  Format.fprintf ppf "%a" (pprint_many_box brk "[ " "; " "]" f) x

let rec pprint_many brk s f ppf = function
  | []              -> ()
  | [x]             -> Format.fprintf ppf "%a" f x
  | x::xs' when brk -> Format.fprintf ppf "%a%s@," f x s; pprint_many brk s f ppf xs'
  | x::xs'          -> Format.fprintf ppf "%a%s" f x s ; pprint_many brk s f ppf xs'

let pprint_maybe f ppf = function
  | Some x -> Format.fprintf ppf "Some %a" f x
  | None   -> Format.fprintf ppf "None"

let pprint_int ppf i =
  Format.fprintf ppf "%d" i

let pprint_int_o = pprint_maybe pprint_int
(*
let pprint_int_o ppf = function
  | None -> Format.fprintf ppf "None" 
  | Some d -> Format.fprintf ppf "Some(%d)" d
*)

let pprint_str ppf s =
  Format.fprintf ppf "%s" s

let pprint_ints ppf is = 
  pprint_many_brackets false (fun ppf i -> Format.fprintf ppf "%d" i) ppf is

let pprint_pretty_ints ppf is = 
  is |> List.map string_of_int |> String.concat ";" |> Format.fprintf ppf "[%s]"

let pprint_tuple pp1 pp2 ppf (x1, x2) = 
  Format.fprintf ppf "(%a, %a)" pp1 x1 pp2 x2

let rec subsets n = function
  | _ when n <= 0 
    -> [[]]
  | xs when n > List.length xs->
      []
  | x::xs 
    -> (List.map (fun ys -> x :: ys) (subsets (n-1) xs))
    ++ (subsets n xs)
  | _ -> assertf "Misc.subsets"

let choose b f g = if b then f else g

let liftfst2 (f: 'a -> 'a -> 'b) (x: 'a * 'c) (y: 'a * 'c): 'b =
  f (fst x) (fst y)

let curry   = fun f x y   -> f (x,y)
let uncurry = fun f (x,y) -> f x y
let flip    = fun f x y   -> f y x

let maybe_bool = function
  | Some _ -> true
  | None   -> false

module type EMapType = sig
  include Map.S
  val extendWith   : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val extend       : 'a t -> 'a t -> 'a t
  val filter       : (key -> 'a -> bool) -> 'a t -> 'a t
  val of_list      : (key * 'a) list -> 'a t
  val to_list      : 'a t -> (key * 'a) list
  val length       : 'a t -> int
  val domain       : 'a t -> key list
  val range        : 'a t -> 'a list
  val join         : 'a t -> 'b t -> ('a * 'b) t
  val adds         : key -> 'a list -> 'a list t -> 'a list t
  val of_alist     : (key * 'a) list -> 'a list t
  val finds        : key -> 'a list t -> 'a list
  val safeFind     : key -> 'a t -> string -> 'a
  val safeAdd      : key -> 'a -> 'a t -> string -> 'a t
  val single       : key -> 'a -> 'a t
  val map_partial  : ('a -> 'b option) -> 'a t -> 'b t
  val maybe_find   : key -> 'a t -> 'a option
  val find_default : 'a -> key -> 'a t -> 'a
  val frequency    : key list -> int t
end

module type ESetType = sig
  include Set.S
  val of_list : elt list -> t
end

module ESet (K: Set.OrderedType) = 
  struct
    include Set.Make(K)
    let of_list = List.fold_left (flip add) empty  
end

module type EOrderedType = sig
  include Map.OrderedType 
  val print : Format.formatter -> t -> unit
end

(* module EMap (K: Map.OrderedType) = *) 
module EMap (K: EOrderedType) = 
  struct
    include Map.Make(K)

    let extendWith (f: key -> 'a -> 'a -> 'a) (m1: 'a t) (m2: 'a t) =
      fold begin fun k v m -> 
        let v' = if mem k m then f k v (find k m) else v in
        add k v' m
      end m2 m1 
    
    let extend (m1: 'a t)  (m2: 'a t) : 'a t = fold add m2 m1

    (* in 3.12 *)
    let filter (f: key -> 'a -> bool) (m: 'a t) : 'a t =  
      fold (fun x y m -> if f x y then add x y m else m) m empty 
    
    let of_list (kvs : (key * 'a) list) = 
      List.fold_left (fun m (k, v) -> add k v m) empty kvs

        (* in 3.12 -- bindings *)
    let to_list (m : 'a t) : (key * 'a) list = 
      fold (fun k v acc -> (k,v)::acc) m [] 

    (* in 3.12 -- cardinality *)
    let length (m : 'a t) : int = 
      fold (fun _ _ i -> i+1) m 0

    (* in 3.12 -- singleton *)
    let single k v = add k v empty

    let domain m =
      fold (fun k _ acc -> k :: acc) m []

    let range (m : 'a t) : 'a list = 
      fold (fun _ v acc -> v :: acc) m []
     
    let join (m1 : 'a t) (m2 : 'b t) : ('a * 'b) t =
      mapi begin fun k v1 ->
        let _  = asserts (mem k m2) "EMap.join" in
        (v1, find k m2) 
      end m1

    let maybe_find k m = 
      try Some (find k m) with Not_found -> None

    let find_default d k m = 
      maybe_default (maybe_find k m) d 

    (* let finds k m = try find k m with Not_found -> [] *)
    let finds k m = find_default [] k m

    let adds (k: key) (vs: 'a list) (m : ('a list) t) : 'a list t = 
      add k (vs ++ find_default [] k m) m

    let of_alist (kvs : (key * 'a) list) =
      List.fold_left (fun m (k, v) -> adds k [v] m) empty kvs
     
    let frequency (ks : key list) : int t =
      List.fold_left (fun m k -> 
        add k (1 + (find_default 0 k m)) m
      ) empty ks 

    let safeFind k m msg =
      try find k m with Not_found -> 
        let err = Format.fprintf Format.str_formatter 
                    "ERROR: safeFind (%s): %a" msg K.print k; 
                  Format.flush_str_formatter ()
        in failwith err

    let safeAdd k v m msg =
      if mem k m then 
        let err = Format.fprintf Format.str_formatter 
                    "ERROR: safeAdd (%s): %a" msg K.print k; 
                  Format.flush_str_formatter ()
        in failwith err
      else add k v m

    let map_partial f m = 
      fold (fun x yo m -> match yo with Some y -> add x y m | _ -> m) (map f m) empty 
  end

module type KeyValType =
  sig
    type t
    val compare : t -> t -> int
    val print : Format.formatter -> t -> unit 

    type v
    val default : v
  end

module MapWithDefault (K: KeyValType) =
  struct
    include EMap(K)
    let find (i: K.t) (m: K.v t): K.v =
      try find i m with Not_found -> K.default
  end

module IntMap = 
  EMap
  (struct
    type t = int
    let compare i1 i2 = compare i1 i2
    let print         = pprint_int
  end)

module IntSet =
  ESet
  (struct
    type t = int
    let compare i1 i2 =
      compare i1 i2
  end)

module IntIntMap = 
  EMap 
  (struct
    type t = int * int
    let compare i1 i2 = compare i1 i2
    let print ppf (i1, i2) = Format.fprintf ppf "(%d, %d)" i1 i2
   end)

module StringMap = 
  EMap 
  (struct
    type t = string 
    let compare i1 i2 = compare i1 i2
    let print ppf s   = Format.fprintf ppf "%s" s
  end)

module StringSet =
  ESet
  (struct
    type t = string
    let compare i1 i2 = compare i1 i2
  end)

(* 
let sm_join sm1 sm2 = 
  StringMap.mapi (fun k v1 ->
    let v2 = asserts (StringMap.mem k sm2) "sm_join"; StringMap.find k sm2 in
    (v1, v2)
  ) sm1

let sm_extend sm1 sm2 =
  StringMap.fold StringMap.add sm2 sm1 

let sm_filter f sm = 
  StringMap.fold begin fun x y sm -> 
    if f x y then StringMap.add x y sm else sm 
  end sm StringMap.empty 

let sm_of_list kvs = 
  List.fold_left (fun sm (k,v) -> StringMap.add k v sm) StringMap.empty kvs

let sm_to_list sm = 
  StringMap.fold (fun k v acc -> (k,v)::acc) sm [] 

let sm_to_range sm = 
  sm |> sm_to_list |> List.map snd
*)

let sm_print_keys name sm =
  sm |> StringMap.to_list 
     |> List.map fst 
     |> String.concat ", "
     |> Printf.printf "%s : %s \n" name

let foldn f n b = 
  let rec foo acc i = 
    if i >= n then acc else foo (f acc i) (i+1) 
  in foo b 0 

let rec range i j = 
  if i >= j then [] else i::(range (i+1) j)

let dump s = 
  print_string s; flush stdout

let mapn f n = 
  foldn (fun acc i -> (f i) :: acc) n [] 
  |> List.rev

let chop_last = function
  | [] -> failure "ERROR: Misc.chop_last"
  | xs -> xs |> List.rev |> List.tl |> List.rev

let list_snoc xs = 
  match List.rev xs with 
  | [] -> assertf "list_snoc with empty list!"
  | h::t  -> h, List.rev t

let negfilter f xs = 
  List.fold_left (fun acc x -> if f x then acc else x::acc) [] xs 
  |> List.rev

let get_option d = function  
  | Some x -> x 
  | None   -> d

let list_somes xs =
  xs |> List.fold_left begin fun acc -> function 
          | Some x -> x :: acc 
          | None   -> acc 
        end []
     |> List.rev

(* let map_partial f = list_somes <.> List.map f  *)

let map_partial f xs =
  List.rev 
    (List.fold_left 
      (fun acc x -> 
        match f x with
        | None   -> acc
        | Some z -> (z::acc)) [] xs)


let fold_left_partial f b xs =
  List.fold_left begin fun b xo ->
    match xo with
      | Some x -> f b x
      | None   -> b
  end b xs

let list_reduce msg f = function
  | []    -> assertf "ERROR: list_reduce with empty list: %s" msg 
  | x::xs -> List.fold_left f x xs

let nonnull = function
  | [] -> false
  | _  -> true

(*
let list_is_empty = function
  | [] -> true
  | _::_ -> false
*)

let list_max x xs = 
  List.fold_left max x xs

let list_min x xs = 
  List.fold_left min x xs

let list_max_with msg f = function
  | []    -> assertf "ERROR: list_max_with with empty list: %s" msg 
  | x::xs -> List.fold_left (fun acc x -> if f x > f acc then x else acc) x xs

let rec take_max n = function
  | x :: xs when n > 0 -> x :: take_max (n - 1) xs
  | _                  -> []
    
let rec drop n = function
  | x :: xs when n > 0 -> drop (n - 1) xs
  | []      when n > 0 -> assertf "ERROR: dropped too many"
  | xs -> xs

let getf a i fmt = 
  try a.(i) with ex -> assertf fmt

let do_catchu f x g =
  try f x with ex -> (g ex; raise ex)

let do_catchf s f x =
  try f x with ex -> 
    assertf "%s hits exn: %s \n" s (Printexc.to_string ex)

let do_catch s f x =
  try f x with ex -> 
     (Printf.printf "%s hits exn: %s \n" s (Printexc.to_string ex); raise ex) 

let do_catch_ret s f x y = 
  try f x with ex -> 
     (Printf.printf "%s hits exn: %s \n" s (Printexc.to_string ex); y) 

let do_memo memo f args key = 
  try Hashtbl.find memo key with Not_found ->
    let rv = f args in
    let _ = Hashtbl.replace memo key rv in
    rv

let do_bimemo fmemo rmemo f args key =
  try Hashtbl.find fmemo key with Not_found ->
    let rv = f args in
    let _ = Hashtbl.replace fmemo key rv in
    let _ = Hashtbl.replace rmemo rv key in
    rv

let rec exists_maybe f = function
  | []    -> None
  | x::xs -> (match f x with None -> exists_maybe f xs | z -> z)

let map_pair   = fun f (x1, x2)     -> (f x1, f x2)
let map_triple = fun f (x1, x2, x3) -> (f x1, f x2, f x3)
let app_fst    = fun f (a, b)       -> (f a, b)
let app_snd    = fun f (a, b)       -> (a, f b)
let app_fst3   = fun f (a, b, c)    -> (f a, b, c)

let app_snd3   = fun f (a, b, c)    -> (a, f b, c)

let app_thd3   = fun f (a, b, c)    -> (a, b, f c)
let pad_snd    = fun f x            -> (x, f x)
let pad_fst    = fun f y            -> (f y, y)
let tmap2      = fun (f, g) x       -> (f x, g x)
let tmap3      = fun (f, g, h) x    -> (f x, g x, h x)
let iter_fst   = fun f (a, b)       -> f a
let iter_snd   = fun f (a, b)       -> f b

let split3 lst =
  List.fold_right (fun (x, y, z) (xs, ys, zs) -> (x :: xs, y :: ys, z :: zs)) lst ([], [], [])

let split4 lst =
  List.fold_right (fun (w, x, y, z) (ws, xs, ys, zs) -> (w :: ws, x :: xs, y :: ys, z :: zs)) lst ([], [], [], [])

let twrap s f x =
  let _  = Printf.printf "calling %s \n" s in
  let rv = f x in
  let _  = Printf.printf "returned from %s \n" s in
  rv

let mapfold_rev f b xs = 
  List.fold_left begin fun (acc, ys) x -> 
    let (acc', y) = f acc x in 
    (acc', y::ys)
  end (b, []) xs

let mapfold f b xs =
  mapfold_rev f b xs 
  |> app_snd List.rev 

let rootsBy leq xs = 
  let notDomBy x = not <.> (leq x) in
  let rec loop acc = function
    | [] -> 
        acc
    | (x::xs) ->
        let acc', xs' = map_pair (List.filter (notDomBy x)) (acc, xs) in
        loop (x::acc') xs'
  in loop [] xs

let cov_filter cov f xs = 
  let rec loop acc = function
    | [] -> 
        acc
    | (x::xs) when f x ->
        let covs, uncovs = List.partition (cov x) xs in
        loop ((x, covs) :: acc) uncovs  
    | (_::xs) ->
      loop acc xs
  in loop [] xs

let filter f xs = 
  List.fold_left (fun xs' x -> if f x then x::xs' else xs') [] xs
  |> List.rev

let iter f xs = 
  List.fold_left (fun () x -> f x) () xs

let map2 f xs ys = 
  let _ = asserti (List.length xs = List.length ys) "Misc.map2" in
  List.map2 f xs ys

let map f xs = 
  List.rev_map f xs |> List.rev

let flatten xss =
  xss
  |> List.fold_left (fun acc xs -> xs ++ acc) []
  |> List.rev

let flatsingles xss =
  xss |> List.fold_left (fun acc -> function [x] -> x::acc | _ -> assertf "flatsingles") []
      |> List.rev

let splitflatten xsyss = 
  let xss, yss = List.split xsyss in
  (flatten xss, flatten yss)

let splitflatten3 xsyszss =
  let xss, yss, zss = split3 xsyszss in
    (flatten xss, flatten yss, flatten zss)

let flap f xs =
  xs |> List.rev_map f |> flatten |> List.rev

let flap_pair f = splitflatten <.> map f

let tr_rev_flatten xs =
  List.fold_left (fun x xs -> x ++ xs) [] xs

let tr_rev_flap f xs =
  List.fold_left (fun xs x -> (f x) ++ xs) [] xs

let rec fast_unflat ys = function
  | x :: xs -> fast_unflat ([x] :: ys) xs
  | [] -> ys

let dup x = (x, x)


let rec rev_perms s = function
  | [] -> s
  | e :: es -> rev_perms 
    (tr_rev_flap (fun e -> List.rev_map (fun s -> e :: s) s) e) es 

let product = function
  | e :: es -> rev_perms (fast_unflat [] e) es
  | es -> es 

let pairs xs =
  let rec pairs_aux ps = function
    | [] -> ps
    | x :: xs -> pairs_aux (List.fold_left (fun ps y -> (x, y) :: ps) ps xs) xs
  in pairs_aux [] xs

let cross_product xs ys = 
  map begin fun x ->
    map begin fun y ->
      (x,y)
    end ys
  end xs
  |> flatten

let rec cross_flatten = function
  | []      -> 
      [[]]
  | xs::xss ->
      map begin fun x ->
        map begin fun ys ->
          (x::ys)
        end (cross_flatten xss)
      end xs
      |> flatten


let append_pref p s =
  (p ^ "." ^ s)


let fsort f xs =
  let cmp = fun (k1,_) (k2,_) -> compare k1 k2 in
  xs |> map (fun x -> ((f x), x)) 
     |> List.sort cmp 
     |> map snd

let sort_and_compact ls =
  let rec _sorted_compact l = 
    match l with
	h1::h2::tl ->
	  let rest = _sorted_compact (h2::tl) in
	    if h1 = h2 then rest else h1::rest
      | tl -> tl
  in
    _sorted_compact (List.sort compare ls)   

let sort_and_compact xs = 
  List.sort compare xs 
  |> List.fold_left 
       (fun ys x -> match ys with
        | y::_ when x=y -> ys
        | _::_          -> x::ys
        | []            -> [x])
       [] 
  |> List.rev

let hashtbl_to_list t = 
  Hashtbl.fold (fun x y l -> (x,y)::l) t []

let hashtbl_keys t = 
  Hashtbl.fold (fun x y l -> x::l) t []
  |> sort_and_compact

let hashtbl_invert t = 
  let t' = Hashtbl.create 17 in
  hashtbl_to_list t 
  |> List.iter (fun (x,y) -> Hashtbl.replace t' y x) 
  |> fun _ -> t'


let distinct xs = 
 List.length xs = List.length (sort_and_compact xs)

(** repeats f: unit - > unit i times *)
let rec repeat_fn f i = 
  if i = 0 then ()
  else (f (); repeat_fn f (i-1))

(* chop s chopper returns ([x;y;z...]) if s = x.chopper.y.chopper ...*)
let chop s chopper = Str.split (Str.regexp chopper) s  

(* like chop only the chop is by chop+ *)
let chop_star chopper s = 
    Str.split (Str.regexp (Printf.sprintf "[%s+]" chopper)) s

let bounded_chop s chopper i = Str.bounded_split (Str.regexp chopper) s i 

let is_prefix p s = 
  let (ls, lp) = (String.length s, String.length p) in
  if ls < lp
    then false
  else
    (String.sub s 0 lp) = p

let is_substring s subs = 
  let reg = Str.regexp subs in
  try ignore(Str.search_forward reg s 0); true
  with Not_found -> false

let replace_substring src dst s =
  Str.global_replace (Str.regexp src) dst s

let is_suffix suffix s = 
  let k = String.length suffix
  and n = String.length s in
  (n-k >= 0) && Str.string_match (Str.regexp suffix) s (n-k)

let iteri f xs =
  List.fold_left (fun i x -> f i x; i+1) 0 xs
  |> ignore

let numbered_list xs =
  xs |> List.fold_left (fun (i, acc) x -> (i+1, (i,x)::acc)) (0,[]) 
     |> snd 
     |> List.rev 

exception FalseException

let sm_protected_add fail k v sm = 
  if not (StringMap.mem k sm) then StringMap.add k v sm else 
    if not fail then sm else 
      assertf "protected_add: duplicate binding for %s \n" k

let hashtbl_to_list_all t = 
  hashtbl_keys t |> map (Hashtbl.find_all t) 

let clone x n =
  let rec f n xs = if n <= 0 then xs else f (n-1) (x::xs) in
  f n []

let single x = [x]

let distinct xs = 
  List.length (sort_and_compact xs) = List.length xs

let trunc i j = 
  let (ai,aj) = (abs i, abs j) in
  if aj <= ai then j else ai*j/aj 

let map_to_string f xs = 
  String.concat "," (List.map f xs)

let suffix_of_string = fun s i -> String.sub s i (String.length s - 1)

(* [count_map xs] = fun x -> number of times x appears in xs if non-zero *)
let count_map rs =
  List.fold_left begin fun m r -> 
      let c = try IntMap.find r m with Not_found -> 0 in
      IntMap.add r (c+1) m
  end IntMap.empty rs

let o2s f = function
  | Some x -> "Some "^ (f x)
  | None   -> "None"

let fixpoint f x =
  let rec acf b x =
    let x', b' = f x in
    if b' then acf true x' else (x', b) in
  acf false x


let fsprintf f p = 
  Format.fprintf Format.str_formatter "@[%a@]" f p;
  Format.flush_str_formatter ()

let rec same_length l1 l2 = match l1, l2 with
  | [], []           -> true
  | _ :: xs, _ :: ys -> same_length xs ys
  | _                -> false

let ex_one s = function
  | [x]    -> x
  | _ :: _ -> failwith s
  | _      -> failwith (s ^ ". empty")

let only_one s = function
    x :: [] -> Some x
  | _ :: _  -> failwith s
  | []      -> None

let maybe_one = function
  | [x] -> Some x
  | _   -> None


let int_of_bool b = if b then 1 else 0

(*****************************************************************)
(******************** Mem Management *****************************)
(*****************************************************************)

open Gc
(* open Format *)

let pprint_gc s =
  (*printf "@[Gc@ Stats:@]@.";
  printf "@[minor@ words:@ %f@]@." s.minor_words;
  printf "@[promoted@ words:@ %f@]@." s.promoted_words;
  printf "@[major@ words:@ %f@]@." s.major_words;*)
  (*printf "@[total allocated:@ %fMB@]@." (floor ((s.major_words +. s.minor_words -. s.promoted_words) *. (4.0) /. (1024.0 *. 1024.0)));*)

  Format.printf "@[total allocated:@ %fMB@]@." (floor ((allocated_bytes ()) /. (1024.0 *. 1024.0)));
  Format.printf "@[minor@ collections:@ %i@]@." s.minor_collections;
  Format.printf "@[major@ collections:@ %i@]@." s.major_collections;
  Format.printf "@[heap@ size:@ %iMB@]@." (s.heap_words * 4 / (1024 * 1024));
  (*printf "@[heap@ chunks:@ %i@]@." s.heap_chunks;
  (*printf "@[live@ words:@ %i@]@." s.live_words;
  printf "@[live@ blocks:@ %i@]@." s.live_blocks;
  printf "@[free@ words:@ %i@]@." s.free_words;
  printf "@[free@ blocks:@ %i@]@." s.free_blocks;
  printf "@[largest@ free:@ %i@]@." s.largest_free;
  printf "@[fragments:@ %i@]@." s.fragments;*)*)
  Format.printf "@[compactions:@ %i@]@." s.compactions;
  (*printf "@[top@ heap@ words:@ %i@]@." s.top_heap_words*) ()

let dump_gc s =
  Format.printf "@[%s@]@." s;
  pprint_gc (Gc.quick_stat ())


let append_to_file f s = 
  let oc = Unix.openfile f [Unix.O_WRONLY; Unix.O_APPEND; Unix.O_CREAT] 420  in
  ignore (Unix.write oc s 0 ((String.length s)-1) ); 
  Unix.close oc

(*
let with_out_file file f =
  let oc = open_out file in
    f oc;
    close_out oc
*)

let display_tick = fun () -> print_now "."

let display_tick = 
  let icona = [| "|"; "/" ; "-"; "\\" |] in
  let pos   = ref 0 in
  fun () -> 
    let k = !pos in
    let _ = print_now ("\b."^icona.(k)) in
    let _ = pos := (k + 1) mod 4 in
    ()

let with_out_file file f = file |> open_out >> f |> close_out

let write_to_file f s =
  with_out_file f (fun oc -> output_string oc s)

let with_out_formatter file f =
  with_out_file file (fun oc -> f (Format.formatter_of_out_channel oc))

let get_unique =
  let cnt = ref 0 in
  (fun () -> let rv = !cnt in incr cnt; rv)

let lines_of_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try 
    while true; do
      lines := input_line chan :: !lines
    done; [] 
  with End_of_file ->
    close_in chan;
    List.rev !lines

let map_lines_of_file infile outfile f =
  let ic = open_in infile in
  let oc = open_out outfile in
  try
    while true; do
      ic |> input_line |> f |> output_string oc
    done;
  with End_of_file -> 
    (close_in ic; close_out oc)

let maybe_cons m xs = match m with
  | None -> xs
  | Some x -> x :: xs

let maybe_list xs = 
  List.fold_right maybe_cons xs []

let rec list_first_maybe f = function
  | x::xs -> begin match f x with 
              | Some y -> Some y 
              | _      -> list_first_maybe f xs
             end
  | []    -> None

let list_find_maybe f xs =
  try some <| List.find f xs with Not_found -> None

let list_assoc_maybe k kvs =
  try Some (List.assoc k kvs) with Not_found -> None

let list_assoc_default d kvs k =
  try List.assoc k kvs with Not_found -> d

let list_assoc_flip xs = 
  let r (x, y) = (y, x) in
    List.map r xs

let fold_lefti f b xs =
  List.fold_left (fun (i,b) x -> ((i+1), f i b x)) (0,b) xs

let mapi f xs = 
  xs |> fold_lefti (fun i acc x -> (f i x) :: acc) [] 
     |> snd |> List.rev

let index_from n xs = 
  let is = range n (n + List.length xs) in
  List.combine is xs

let fold_left_flip f b xs =
  List.fold_left (flip f) b xs

let fold_left_swap f xs b =
  List.fold_left f b xs

let rec map3 f xs ys zs = match (xs, ys, zs) with
  | ([], [], []) -> []
  | (x :: xs, y :: ys, z :: zs) -> f x y z :: map3 f xs ys zs
  | _ -> assert false

let rec fold_right3 f xs ys zs acc = match xs, ys, zs with
  | x :: xs, y :: ys, z :: zs -> f x y z (fold_right3 f xs ys zs acc)
  | [], [], []                -> acc
  | _                         -> assert false

let rec fold_left3 f acc xs ys zs = match xs, ys, zs with
  | x :: xs, y :: ys, z :: zs -> fold_left3 f (f acc x y z) xs ys zs
  | [], [], []                -> acc
  | _                         -> assert false

let zip_partition xs bs =
  let (xbs, xbs') = List.partition snd (List.combine xs bs) in
  (List.map fst xbs, List.map fst xbs')

let rec map4 f ws xs ys zs = match ws, xs, ys, zs with
  | [], [], [], []                     -> []
  | w :: ws, x :: xs, y :: ys, z :: zs -> f w x y z :: map4 f ws xs ys zs
  | _                                  -> asserti false "map4"; assert false


let rec perms es =
  match es with
    | s :: [] ->
        List.map (fun c -> [c]) s
    | s :: es ->
        flap (fun c -> List.map (fun d -> c :: d) (perms es)) s
    | [] ->
        []

let flap2 f xs ys = 
  List.flatten (List.map2 f xs ys)

let flap3 f xs ys zs =
  List.flatten (map3 f xs ys zs)

let combine msg xs ys =
  let _ = asserts (List.length xs = List.length ys) "%s" msg in
  List.combine xs ys

let combine3 xs ys zs =
  map3 (fun x y z -> (x, y, z)) xs ys zs

let combine4 ws xs ys zs =
  map4 (fun w x y z -> (w, x, y, z)) ws xs ys zs

let tr_partition f xs =
  List.fold_left begin fun (xs,ys) z -> 
    if f z 
    then (z::xs, ys) 
    else (xs, z::ys)
  end ([],[]) xs

let either_partition f xs =
  List.fold_left begin fun (xs, ys) z -> 
    match f z with
    | Left x  -> (x::xs, ys)
    | Right y -> (xs, y::ys)
  end ([], []) xs

(* these do odd things with order for performance 
 * it is possible that fast is a misnomer *)
let fast_flatten xs =
  List.fold_left (++) [] xs

let fast_append v v' =
  let (v, v') = if List.length v > List.length v' then (v', v) else (v, v') in
  List.rev_append v v'

let fast_flap f xs =
  List.fold_left (fun xs x -> List.rev_append (f x) xs) [] xs

let rec fast_unflat ys = function
  | x :: xs -> fast_unflat ([x] :: ys) xs
  | [] -> ys

let rec rev_perms s = function
  | [] -> s
  | e :: es -> rev_perms 
    (fast_flap (fun e -> List.rev_map (fun s -> e :: s) s) e) es 

let rev_perms = function
  | e :: es -> rev_perms (fast_unflat [] e) es
  | es -> es 

let tflap2 (e1, e2) f =
  List.fold_left (fun bs b -> List.fold_left (fun aas a -> f a b :: aas) bs e1) [] e2

let tflap3 (e1, e2, e3) f =
  List.fold_left begin fun cs c -> 
    List.fold_left begin fun bs b -> 
      List.fold_left begin fun aas a -> 
        f a b c :: aas
      end bs e1
    end cs e2
  end[] e3

let rec expand f xs ys =
  match xs with
  | []    -> ys
  | x::xs -> let (xs', ys') = f x in
             expand f (xs' ++  xs) (ys' ++ ys)

let rec get_first f = function
  | x::xs when f x -> Some x 
  | _::xs          -> get_first f xs
  | []             -> None

let join f xs ys = 
  let rec fuse acc xs ys = 
    match xs, ys with 
    | [],_ | _, []                              -> List.rev acc
    | ((kx, _)::xs', (ky,_)::_  ) when kx < ky  -> fuse acc xs' ys
    | ((kx, _)::_  , (ky,_)::ys') when kx > ky  -> fuse acc xs  ys' 
    | ((kx, x)::xs', (ky,y)::ys') (* kx = ky *) -> fuse ((x,y)::acc) xs' ys' in
  let xs' = List.map (fun x -> (f x, x)) xs |> List.sort compare in
  let ys' = List.map (fun y -> (f y, y)) ys |> List.sort compare in
  fuse [] xs' ys'

let hashtbl_find_default d t x =
  try Hashtbl.find t x with Not_found -> d

let frequency (xs : 'a list) : ('a * int) list = 
  let t = Hashtbl.create 17 in
  List.iter begin fun x ->
    let n =  hashtbl_find_default 0 t x in
    Hashtbl.replace t x (n + 1)
  end xs;
  hashtbl_to_list t

let kgroupby (f: 'a -> 'b) (xs: 'a list): ('b * 'a list) list =
  let t        = Hashtbl.create 17 in
  let lookup x = try Hashtbl.find t x with Not_found -> [] in
  (* build table *)
  List.iter begin fun x -> 
    Hashtbl.replace t (f x) (x :: lookup (f x))
  end xs;
  (* build cluster *)
  Hashtbl.fold (fun k xs xxs -> (k, xs) :: xxs) t []



let groupby (f: 'a -> 'b) (xs: 'a list): 'a list list =
  kgroupby f xs |> List.map (snd <+> List.rev)

let full_join f xs ys =
     (xs, ys)
  |> map_pair (kgroupby f)
  |> uncurry (join fst)
  |> flap (map_pair snd <+> uncurry cross_product)

let exists_pair (f: 'a -> 'a -> bool) (xs: 'a list): bool =
  fst (List.fold_left (fun (b, ys) x -> (b || List.exists (f x) ys, x :: ys)) (false, []) xs)

let rec find_pair (f: 'a -> 'a -> bool): 'a list -> 'a * 'a = function
  | []    -> raise Not_found
  | x::xs -> try (x, List.find (f x) xs) with Not_found -> find_pair f xs

let rec is_unique = function
  | []      -> true
  | x :: xs -> if List.mem x xs then false else is_unique xs

let map_opt f = function
  | Some o -> Some (f o)
  | None -> None

let resl_opt f = function
  | Some o -> f o
  | None -> []

let resi_opt f = function
  | Some o -> f o
  | None -> ()

let opt_iter f l = 
  List.iter (resi_opt f) l

let array_findi p arr =
  let rec look i =
    if i < 0 then raise Not_found else
      if p arr.(i) then i else look i - 1
  in look (Array.length arr - 1)

let array_to_index_list a =
  Array.fold_left (fun (i, rv) v -> (i+1,(i,v)::rv)) (0,[]) a
  |> snd
  |> List.rev


let hashtbl_of_list xys = 
  let t = Hashtbl.create 37 in
  let _ = List.iter (fun (x,y) -> Hashtbl.add t x y) xys in
  t

let hashtbl_of_list_with kf xs = 
  xs |>: pad_fst kf |> hashtbl_of_list

let array_flapi f a =
  Array.fold_left (fun (i, acc) x -> (i+1, (f i x) :: acc)) (0,[]) a
  |> snd 
  |> List.rev
  |> flatten

let array_fold_lefti f acc a =
  Array.fold_left (fun (i, acc) x -> (i + 1, f i acc x)) (0, acc) a |> snd

let array_map2 f xa ya = 
  Array.mapi (fun i x -> f x (ya.(i))) xa

let array_rev_iteri f a =
  for i = Array.length a - 1 downto 0 do
    f i a.(i)
  done

exception NotForall

let array_forall f a =
  try
    Array.iter (fun e -> if f e then () else raise NotForall) a; true
  with NotForall ->
    false

let array_combine a1 a2 = 
  asserts (Array.length a1 = Array.length a2) "array_combine";
  Array.init (Array.length a1) (fun i -> (a1.(i), a2.(i)))


let compose f g a = f (g a)


let rec gcd (a: int) (b: int): int =
  if b = 0 then a else gcd b (a mod b)

let lcm (a: int) (b: int): int =
  if a = 0 then a else (abs (a * b)) / (gcd a b)

let mk_int_factory () =
  let id = ref (-1) in
    ((fun () -> incr id; !id), (fun () -> id := -1))

let mk_char_factory () =
  let (fresh_int, reset_fresh_int) = mk_int_factory () in
    ((fun () -> Char.chr (fresh_int () + Char.code 'a')), reset_fresh_int)

let mk_string_factory s =
  let (fresh_int, reset_fresh_int) = mk_int_factory () in
    ((fun () -> s^(string_of_int (fresh_int ()))), reset_fresh_int)

let swap (x,y) = (y,x)

(* ('a * (int * 'b) list) list -> (int * ('a * 'b) list) list *)
let transpose x_iys_s = 
  let t = Hashtbl.create 17 in
  List.iter begin fun (x, iys) ->
    List.iter begin fun (i, y) -> 
      Hashtbl.add t i (x,y) 
    end iys
  end x_iys_s; 
  hashtbl_keys t |> List.map (fun i -> (i, Hashtbl.find_all t i))

let basename_no_extension fname =
  fname |> Filename.basename |> Filename.chop_extension

let absolute_name name =
  if not (Filename.is_relative name) then name else
    let b    = Filename.basename name in
    let d    = Filename.dirname name in
    let dir  = Sys.getcwd () in
    let _    = Sys.chdir (Filename.concat dir d) in
    let dir' = Sys.getcwd () in
    let rv   = Filename.concat dir' b in
    let _    = Sys.chdir dir in
    rv

let cardinality = fun xs -> xs |> sort_and_compact |> List.length
let disjoint    = fun xs ys -> cardinality xs + cardinality ys = cardinality (xs ++ ys)

let bracket (l : unit -> unit) (r : unit -> unit) (f : unit -> 'a) : 'a = 
  try () |> l |> f >> (fun _ -> r ())
  with ex -> assertf "bracket hits exn: %s \n" (Printexc.to_string ex)

(*
let with_ref_at x v f =
  let oldv  = !x in 
  bracket (fun _ -> x := v) (fun _ -> x := oldv) f 
*)

let with_ref_at x v f = 
  let oldv = !x        in 
  let _    = x := v    in
  let res  = f ()      in
  let _    = x := oldv in
  res



let rec isPrefix = function
  | ([], _)                   -> true
  | (x::xs, y::ys) when x = y -> isPrefix (xs, ys)
  | _                         -> false

let find_first_true f lo hi =
  let rec go lo hi = 
    let mid = lo + ((hi - lo) / 2) in
    match () with
    | _ when lo >= hi    -> None
    | _ when lo = hi - 1 -> Some hi 
    | _ when f mid       -> go lo mid 
    | _                  -> go mid hi 
  in   if f lo then Some lo 
  else if not (f hi) then None 
  else go lo hi

let safeHead msg = function
  | [x] -> x
  | _   -> failwith ("ERROR: safeHead" ^ msg) 

let safeApply pp f x = match f x with
  | Some y -> y
  | None   -> failwith ("ERROR: safeApply " ^ (pp x)) 


