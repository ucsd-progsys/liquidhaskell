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

 
(*************************************************************)
(******************** Solution Management ********************)
(*************************************************************)

module F   = Format
module A   = Ast
module E   = A.Expression
module P   = A.Predicate

module Q   = Qualifier
module QS  = Q.QSet
module Sy  = A.Symbol
module Su  = A.Subst
module SM  = Sy.SMap
module SS  = Sy.SSet
module C   = FixConstraint

module BS  = BNstats
module TP  = TpNull.Prover
module Co  = Constants
module Cg  = FixConfig
module H   = Hashtbl
module PH  = A.Predicate.Hash

module Cx  = Counterexample
module Misc = FixMisc 
module IM  = Misc.IntMap
open Misc.Ops

let mydebug = false 

module Q2S = Misc.ESet (struct
  type t = Sy.t * Sy.t
  let compare x y = compare x y 
end)

module V : Graph.Sig.COMPARABLE with type t = Sy.t = struct
  type t = Sy.t
  let hash    = Sy.to_string <+> H.hash
  let compare = compare
  let equal   = (=) 
end



(*
let tag_of_qual2 = Misc.map_pair tag_of_qual

module Q2S = Misc.ESet (struct
  type t = Q.t * Q.t
  let compare x y = compare (tag_of_qual2 x) (tag_of_qual2 y)
end)

module V : Graph.Sig.COMPARABLE with type t = Q.t = struct
  type t = Q.t
  let hash    = tag_of_qual <+> H.hash
  let compare = fun q1 q2 -> compare (tag_of_qual q1) (tag_of_qual q2)
  let equal   = fun q1 q2 -> tag_of_qual q1 = tag_of_qual q2
end

*)

module Id : Graph.Sig.ORDERED_TYPE_DFT with type t = unit = struct
  type t = unit 
  let default = ()
  let compare = compare 
end

module G   = Graph.Persistent.Digraph.ConcreteLabeled(V)(Id)
module SCC = Graph.Components.Make(G)

type bind = Q.t list

type t   = 
  { tpc  : TP.t
  ; m    : bind SM.t
  ; assm : FixConstraint.soln  (* invariant assumption for K, 
                                 must be a fixpoint wrt constraints *)
  ; qm   : Q.t SM.t            (* map from names to qualifiers *)
  ; qleqs: Q2S.t               (* (q1,q2) \in qleqs implies q1 => q2 *)
  
  (* counterexamples *)
  ; step     : Cx.step         (* which iteration *)
  ; ctrace   : Cx.ctrace 
  ; lifespan : Cx.lifespan 
  
  (* stats *)
  ; stat_simple_refines : int ref 
  ; stat_tp_refines     : int ref 
  ; stat_imp_queries    : int ref 
  ; stat_valid_queries  : int ref 
  ; stat_matches        : int ref 
  ; stat_umatches       : int ref 
  ; stat_unsatLHS       : int ref 
  ; stat_emptyRHS       : int ref 
}

let pprint_ps =
  Misc.pprint_many false ";" P.print 

 
let pprint_dep ppf q = 
  F.fprintf ppf "(%a, %a)" P.print (Q.pred_of_t q) Q.print_args q

let pprint_ds = 
  Misc.pprint_many false ";" pprint_dep

let pprint_qs ppf = 
  F.fprintf ppf "[%a]" (Misc.pprint_many false ";" Q.print)

let pprint_qs' ppf = 
  List.map (fst <+> snd <+> snd <+> fst) <+> pprint_qs ppf 

(*************************************************************)
(************* Breadcrumbs for Cex Generation ****************)
(*************************************************************)

let cx_iter c me = 
  { me with step = me.step + 1 }          

let cx_ctrace b c me = 
  let _ = if mydebug then F.printf "\nPredAbs.refine iter = %d cid = %d b = %b\n" 
                          me.step (C.id_of_t c) b in
  if b then { me with ctrace = IM.adds (C.id_of_t c) [me.step] me.ctrace } else me

let cx_update ks kqsm' me : t = 
  List.fold_left begin fun me k -> 
    let qs    = QS.of_list  (SM.finds k me.m)  in
    let qs'   = QS.of_list  (SM.finds k kqsm') in
    let kills = QS.elements (QS.diff qs qs')   in
    if Misc.nonnull kills 
    then {me with lifespan = SM.adds k [(me.step, kills)] me.lifespan}
    else me
  end me ks

(*************************************************************)
(************* Constructing Initial Solution *****************)
(*************************************************************)

(*

let def_of_pred_qual (p, q) =
  let qp = Q.pred_of_t q in
  match A.unify_pred qp p with
  | Some su -> (p, q, su)
  | None    -> assertf "ERROR: unify q=%s p=%s" (P.to_string qp) (P.to_string p)

let map_of_bindings bs =
  List.fold_left begin fun s (k, ds) -> 
    ds |> List.map Misc.single 
       |> Misc.flip (SM.add k) s
  end SM.empty bs 
*)

let quals_of_bindings bm =
  bm |> SM.range 
     |> Misc.flatten
     (* |> Misc.map (snd <+> fst)  *)
     |> Misc.sort_and_compact
     >> (fun qs -> Co.logPrintf "Quals of Bindings: \n%a" (Misc.pprint_many true "\n" Q.print) qs; flush stdout)

(************************************************************************)
(*************************** Dumping to Dot *****************************) 
(************************************************************************)


module DotGraph = struct
  type t = G.t
  module V = G.V
  module E = G.E
  let iter_vertex               = G.iter_vertex
  let iter_edges_e              = G.iter_edges_e
  let graph_attributes          = fun _ -> [`Size (11.0, 8.5); `Ratio (`Fill (* Float 1.29*))]
  let default_vertex_attributes = fun _ -> [`Shape `Box]
  let vertex_name               = Sy.to_string 
  let vertex_attributes         = fun q -> [`Label (Sy.to_string q)] 
  let default_edge_attributes   = fun _ -> []
  let edge_attributes           = fun (_,(),_) -> [] 
  let get_subgraph              = fun _ -> None
end

module Dot = Graph.Graphviz.Dot(DotGraph) 

let dump_graph s g = 
  s |> open_out 
    >> (fun oc -> Dot.output_graph oc g)
    |> close_out 

let p_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: p_read : unknown kvar %s\n" (Sy.to_string k) in
  SM.find k s.m  |>: (fun q -> ((k, q), Q.pred_of_t q))

(* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds = SM.finds k m in
  let n  = List.length ds  in
  let n' = List.length ds' in 
  let _  = asserts (n = 0 || n' <= n) "PredAbs.update: Non-monotone k = %s |ds| = %d |ds'| = %d \n" (Sy.to_string k) n n' in 
  ((n != n'), SM.add k ds' m)
  (* >> begin fun _ -> 
        if n' > n && n > 0 then 
          print_now  <| Printf.sprintf "OMFG: update k = %s |ds| = %d |ds'| = %d \n" 
                          (Sy.to_string k) n n'
     end
   *)

(* We must ensure there are NO duplicate k-q pairs in the update list.
 * If there are duplicate KVars in the ks then the kqs must be grouped:
 * a "k-q" binding is ONLY preserved  IF #bindings = #copies-of-k
 * If there are NO duplicate KVars there SHOULD BE no duplicate k-q pairs. *)

let group_ks_kqs ks kqs = 
  if (Misc.cardinality ks = List.length ks) then 
    kqs (* no duplicate kvars *) 
  else 
    let km = SM.frequency ks in
    kqs |> Misc.frequency 
        |> Misc.filter (fun ((k, _), n) -> n = SM.find_default 0 k km)
        |> Misc.map fst 

let p_update me ks kqs = 
  (* let _    = print_now (Printf.sprintf "p_update A: |kqs| = %d \n" (List.length kqs)) in *)
  let kqs  = group_ks_kqs ks kqs in
  (* let _    = print_now (Printf.sprintf "p_update B: |kqs| = %d \n" (List.length kqs)) in *)
  let kqsm = SM.of_alist kqs in
  let me   = me |> (!Co.cex <?> BS.time "cx_update" (cx_update ks) kqsm) in 
  List.fold_left begin fun (b, m) k ->
    SM.finds k kqsm 
    |> update m k 
    |> Misc.app_fst ((||) b)
  end (false, me.m) ks
  |> Misc.app_snd (fun m -> { me with m = m })  


(* API *)
let top s ks = 
  ks (* |> List.partition (fun k -> SM.mem k s.m)
     >> (fun (_, badks) -> Co.logPrintf "WARNING: Trueing Unbound KVars = %s \n" (Misc.fsprintf (Misc.pprint_many false "," Sy.print) badks))
     |> fst *)
     |> Misc.flip (p_update s) []
     |> snd

(***************************************************************)
(************************** Refinement *************************)
(***************************************************************)

let rhs_cands s = function
  | C.Kvar (su, k) -> k (* >> (fun k -> print_now ("rhs_cands: k = "^(Sy.to_string k)^"\n")) *)
                        |> p_read s 
                        (* >> (fun xs -> print_now ("rhs_cands: size="^(string_of_int (List.length xs))^" BEGIN \n")) *)
                        |>: (Misc.app_snd (Misc.flip A.substs_pred su))
                        (* >> (fun xs -> print_now ("rhs_cands: size="^(string_of_int (List.length xs))^" DONE\n")) *)
  | _ -> []

let check_tp me env vv t lps =  function [] -> [] | rcs ->
  (* let rv  = TP.set_filter me.tpc env vv lps rcs               in
  let _   = ignore(me.stat_tp_refines    += 1)
          ; ignore(me.stat_imp_queries   += (List.length rcs))
          ; ignore(me.stat_valid_queries += (List.length rv)) 
  in rv *)
  TP.set_filter me.tpc env vv lps rcs
  >> (fun _  -> me.stat_tp_refines    += 1)
  >> (fun _  -> me.stat_imp_queries   += List.length rcs)
  >> (fun rv -> me.stat_valid_queries += List.length rv) 




(* API *)
let read me k = (me.assm k) ++ (if SM.mem k me.m then p_read me k |>: snd else [])

(* API *)
let read_bind s k = failwith "PredAbs.read_bind"

let refine me c =
  let (_,_,ra2s) as r2 = C.rhs_of_t c in
  let k2s = r2 |> C.kvars_of_reft |> List.map snd in
  let rcs = BS.time "rhs_cands" (Misc.flap (rhs_cands me)) ra2s in
  if rcs = [] then
    let _ = me.stat_emptyRHS += 1 in
    (false, me)
  else 
    let lps = BS.time "preds_of_lhs" (C.preds_of_lhs (read me)) c in
    if BS.time "lhs_contra" (List.exists P.is_contra) lps then 
    let _ = me.stat_unsatLHS += 1 in
    let _ = me.stat_umatches += List.length rcs in
    (false, me)
  else 
    let rcs     = List.filter (fun (_,p) -> not (P.is_contra p)) rcs in
    let lt      = PH.create 17 in
    let _       = List.iter (fun p -> PH.add lt p ()) lps in
    let (x1,x2) = List.partition (fun (_,p) -> PH.mem lt p) rcs in
    let _       = me.stat_matches += (List.length x1) in
    let kqs1    = List.map fst x1 in
    (if C.is_simple c 
     then (ignore(me.stat_simple_refines += 1); kqs1) 
     else let senv = C.senv_of_t c in
          let vv   = C.vv_of_t c   in
          let t    = C.sort_of_t c in
          kqs1 ++ (BS.time "check tp" (check_tp me senv vv t lps) x2))
    |> p_update me k2s

let refine me c = 
  let me      = me |> (!Co.cex <?> cx_iter c)     in
  let (b, me) = refine me c                       in
  let me      = me |> (!Co.cex <?> cx_ctrace b c) in
  (b, me)


(***************************************************************)
(****************** Sort Check Based Refinement ****************)
(***************************************************************)

let refts_of_c c =
  [ C.lhs_of_t c ; C.rhs_of_t c] ++ (C.env_of_t c |> C.bindings_of_env |>: snd)

let refine_sort_reft env me ((vv, so, ras) as r) = 
  let env' = SM.add vv r env in 
  let ks   = r |> C.kvars_of_reft |>: snd in
  (* let _    = let s =  String.concat ", " (List.map Sy.to_string ks) in print_now ("\n refine_sort_reft ks = "^s^"\n")  in  *)
  ras 
  |> Misc.flap (rhs_cands me) (* OMFG blowup due to FLAP if kv appears multiple times...*)
  |> Misc.filter (fun (_, p) -> C.wellformed_pred env' p)
  |> List.rev_map fst
(* |> (fun xs -> print_now (Printf.sprintf "refine_sort_reft map: size = %d\n" (List.length xs)); 
                List.rev_map fst xs)
  >> (fun _ -> print_now "\n refine_sort_reft TICK 4 \n")
  *)
  |> p_update me ks
  |> snd

let refine_sort me c =
  let env = C.env_of_t c in
  c (* >> (fun _ -> print_now ("\n refine_sort TICK 0 id = "^(string_of_int (C.id_of_t c))^"\n")) *)
    |> refts_of_c
    |> List.fold_left (refine_sort_reft env) me  
    (* >> (fun _ -> print_now "\n refine_sort TICK 2 \n") *)

(***************************************************************)
(************************* Satisfaction ************************)
(***************************************************************)

let unsat me c = 
  let s        = read me      in
  let (vv,t,_) = C.lhs_of_t c in
  let lps      = C.preds_of_lhs s c  in
  let rhsp     = c |> C.rhs_of_t |> C.preds_of_reft s |> A.pAnd in
  not ((check_tp me (C.senv_of_t c) vv t lps [(0, rhsp)]) = [0])

(****************************************************************)
(************* Minimization: For Prettier Output ****************)
(****************************************************************)

(*
let canonize_subs = 
  Su.to_list <+> List.sort (fun (x,_) (y,_) -> compare x y)

let subst_leq =
  Misc.map_pair canonize_subs <+> Misc.isPrefix
*)

let args_leq q1 q2 =
  let xe1s, xe2s = (Q.args_of_t q1, Q.args_of_t q2) in
  let xe1e2s     = Misc.join fst xe1s xe2s          in
  List.for_all (fun ((_,e1),(_,e2)) -> e1 = e2) xe1e2s 

(* P(v,x,y,z) => Q(v,x) if P => Q held and _intersection_ of args match. *)
let def_leq s q1 q2 = 
     Q2S.mem (Q.name_of_t q1, Q.name_of_t q2) s.qleqs && args_leq q1 q2

let pred_of_bind_name q = 
  let name = q |> Q.name_of_t                 in
  let args = q |> Q.args_of_t |> List.map snd in
  A.pBexp (A.eApp (name, args)) 

let pred_of_bind_raw = Q.pred_of_t 

let pred_of_bind q = 
  if !Co.shortannots 
  then pred_of_bind_name q 
  else pred_of_bind_raw q 

(* API *)
let min_binds s ds = Misc.rootsBy (def_leq s) ds
let min_read s k   = SM.finds k s.m |> min_binds s |>: pred_of_bind
let min_read s k   = if !Co.minquals then min_read s k else read s k
let min_read s k   = BS.time "min_read" (min_read s) k

let close_env qs sm =
  qs |> Misc.flap   (Q.pred_of_t <+> P.support) 
     |> Misc.filter (not <.> Misc.flip SM.mem sm)
     |> Misc.map    (fun x -> (x, Ast.Sort.t_int))
     |> SM.of_list
     |> SM.extend sm

let rename_vv q q' =
  List.combine (Q.all_params_of_t q |>: fst) (Q.all_params_of_t q' |>: fst)
  |> List.filter (fun (x, y) -> not (x = y))
  |> List.map (fun (x, y) -> (y, A.eVar x))
  |> Su.of_list
  |> A.substs_pred (Q.pred_of_t q')
  |> (fun p' -> (q', p'))

let sm_of_qual sm q = 
  q |> Q.all_params_of_t 
    |> SM.of_list 
    |> SM.extend sm

(*  check_leq tp sm q qs = [q' | q' <- qs, Z3 |- q => q'] *)
let check_leq tp sm (q : Q.t) (qs : Q.t list) : Q.t list = 
  let vv  = Q.vv_of_t q in
  let lps = [Q.pred_of_t q] in
  let sm  = q |> sm_of_qual sm |> close_env qs in
  qs |> List.map (rename_vv q) (* (fun q -> (q, Q.pred_of_t q)) *)
     (* >> (List.map fst <+> F.printf "CHECK_TP: %a IN %a \n" Q.print q pprint_qs) *)
     |> TP.set_filter tp sm vv lps
     (* >> F.printf "CHECK_TP: %a OUT %a \n" Q.print q pprint_qs *)

let qimps_of_partition tp sm qs =
  foreach qs begin fun q ->
    let qs' = check_leq tp sm q qs in
    foreach qs' begin fun q' ->
      (q, q')
    end
  end

let wellformed_qual sm q =
  let sm = sm_of_qual sm q in
  A.sortcheck_pred (fun x -> SM.maybe_find x sm) (Q.pred_of_t q)

let qleqs_of_qs ts sm cs ps qs  =
  let tp = TP.create ts sm cs ps         in
  qs |> Misc.filter (wellformed_qual sm)
     |> Misc.groupby (List.map snd <.> Q.all_params_of_t) (* Q.sort_of_t *)
     |> Misc.flap (qimps_of_partition tp sm)
     |> Misc.flatten
     |> Misc.map (Misc.map_pair Q.name_of_t) 
     |> Q2S.of_list

(***************************************************************)
(******************** Qualifier Instantiation ******************)
(***************************************************************)

type qual_binding = (Sy.t * Sy.t) list

(* DEBUG ONLY *)
let print_param ppf (x, t) =
  F.fprintf ppf "%a:%a" Sy.print x Ast.Sort.print t 
let print_params ppf args =
  F.fprintf ppf "%a" (Misc.pprint_many false ", " print_param) args
let print_valid_binding ppf (x,y) =
  F.fprintf ppf "[%a := %a]" Sy.print x Sy.print y
let print_valid_bindings ppf xys =
  F.printf "[%a]" (Misc.pprint_many false "" print_valid_binding) xys

(* 
let dupfree_binding xys : bool = 
  let ys  = List.map snd xys in
  let ys' = Misc.sort_and_compact ys in
  List.length ys = List.length ys'
*)

let varmatch_ctr = ref 0

let varmatch (x, y) = 
  let _ = varmatch_ctr += 1 in
  let (x,y) = Misc.map_pair Sy.to_string (x,y) in
  if x.[0] = '@' then
    let x' = Misc.suffix_of_string x 1 in
    Misc.is_prefix x' y
  else true

let sort_compat t1 t2 = A.Sort.unify [t1] [t2] <> None

(* {{{ DONT DELETE FOR NOW let valid_bindings_sort env (x, t) =
  let _ = failwith "valid_bindings_sort: slow AND incorrect. suppressed!" in
  env |> SM.to_list
      |> Misc.filter (snd <+> C.sort_of_reft <+> (sort_compat t))
      |> Misc.map (fun (y,_) -> (x, y))
      |> Misc.filter varmatch

let valid_bindings env ys (x, t) =
  if !Co.sorted_quals
  then valid_bindings_sort env (x, t)
  else valid_bindings ys x
}}} *)

let wellformed_qual wf f q = 
  q |> Q.pred_of_t 
    |> A.sortcheck_pred f
    (* >> (F.printf "\nwellformed: id = %d q = @[%a@] result %b\n" (C.id_of_wf wf) Q.print q) *)
    (* NEVER uncomment out the above. *)

(********************************************************************************)
(****** Brute Force (Post-Selection based) Qualifier Instantiation **************)
(********************************************************************************)

let is_valid_binding (xys : qual_binding) : bool = 
  List.for_all varmatch xys

let valid_bindings ys (x,_) =
  ys |> List.map (fun y -> (x, y))
     |> List.filter varmatch

let inst_qual env ys evv (q : Q.t) : Q.t list =
  let vve = (Q.vv_of_t q, evv) in
  match Q.params_of_t q with
  | [] ->
      [(Q.inst q [vve])]
  | xts ->
      xts
      (* >> F.printf "\n\ninst_qual: params q = %a: %a" Q.print q print_params          *)
      |> List.map (valid_bindings ys)                       (* candidate bindings    *)
      |> Misc.product                                       (* generate combinations *) 
      (* >> (List.iter (F.printf "\ninst_qual: pre-binds = %a\n" print_valid_bindings)) *)
      |> List.filter is_valid_binding                       (* remove bogus bindings *)
      (* >> (List.iter (F.printf "\ninst_qual: post-binds = %a\n" print_valid_bindings)) *)
      |> List.rev_map (List.map (Misc.app_snd A.eVar))      (* instantiations        *)
      |> List.rev_map (fun xes -> Q.inst q (vve::xes))      (* quals *)
      (* >> (F.printf "\n\ninst_qual: result q = %a:\n%a DONE\n" Q.print q (Misc.pprint_many true "" Q.print)) *)

let inst_vars env = 
  env |> Sy.SMap.to_list 
      |> List.filter (fun (_, (_,so,_)) -> not (A.Sort.is_func so))
      |> List.map fst 

let inst_ext qs wf = 
  let _    = Misc.display_tick () in
  let r    = C.reft_of_wf wf in 
  let ks   = C.kvars_of_reft r |> List.map snd in
  let env  = C.env_of_wf wf in
  let vv   = fst3 r in
  let t    = snd3 r in
  let ys   = inst_vars env   in
  let env' = Misc.maybe_map C.sort_of_reft <.> C.lookup_env (SM.add vv r env) in
  qs |> List.filter (Q.sort_of_t <+> sort_compat t)
     |> Misc.flap   (inst_qual env ys (A.eVar vv))
     |> Misc.filter (wellformed_qual wf env' <&&> C.filter_of_wf wf)
     |> Misc.cross_product ks
     
(********************************************************************************)
(****** Sort Based Qualifier Instantiation **************************************)
(********************************************************************************)

let inst_binds env = 
  env |> SM.to_list 
      |> Misc.map (Misc.app_snd snd3) 
      |> Misc.filter (not <.> A.Sort.is_func <.> snd)

(* [ (su', (x,y) : xys) | (su, xys) <- wkl
                        , (y, ty)   <- yts
                        , varmatch (x, y)
                        , Some su'  <- unifyWith su [tx] [ty] ]  *)

let ext_bindings yts wkl (x, tx) =
  let yts = List.filter (fun (y,_) -> varmatch (x, y)) yts in
  Misc.tr_rev_flap (fun (su, xys) ->
    Misc.map_partial (fun (y, ty) -> 
      match A.Sort.unifyWith su [tx] [ty] with
        | None     -> None
        | Some su' -> Some (su', (x,y) :: xys)
    ) yts
  ) wkl 

let inst_qual_sorted yts vv t q = 
  let (qvv0, t0) :: xts = Q.all_params_of_t q     in
  match A.Sort.unify [t0] [t] with 
    | Some su0 -> 
        xts |> List.fold_left (ext_bindings yts) [(su0, [(qvv0, vv)])]  (* generate subs-bindings *)
            |> List.rev_map (List.rev <.> snd)                          (* extract sorted bindings *)
            |> List.rev_map (List.map (Misc.app_snd A.eVar))            (* instantiations        *)
            |> List.rev_map (Q.inst q)                                  (* quals *)
    | None    -> [] 

let inst_ext_sorted qs wf = 
  let _    = Misc.display_tick ()               in
  let r    = C.reft_of_wf wf                    in 
  let ks   = List.map snd <| C.kvars_of_reft r  in
  let env  = C.env_of_wf wf                     in
  let vv   = fst3 r                             in
  let t    = snd3 r                             in
  let yts  = inst_binds env                     in
  qs |> Misc.flap (inst_qual_sorted yts vv t)
     |> Misc.cross_product ks

(*************************************************************************************)

let inst_ext qs wf =
  if !Co.sorted_quals 
  then inst_ext_sorted qs wf 
  else inst_ext        qs wf
 
let inst_ext qs wf =
  if mydebug then 
    let msg = Printf.sprintf "inst_ext wf id = %d" (C.id_of_wf wf) in
    Misc.trace msg (inst_ext qs) wf
    >> (List.length <+> F.printf "\n\ninst_ext wfid = %d: size = %d\n"  (C.id_of_wf wf))
  else inst_ext qs wf

(* API *)
let inst ws qs =
  Misc.flap (inst_ext qs) ws 
  |> Misc.kgroupby fst 
  |> Misc.map (Misc.app_snd (List.map snd)) 



(*************************************************************************)
(*************************** Creation ************************************)
(*************************************************************************)

let create_qleqs ts sm ps consts qs =
  if !Co.minquals 
  then BS.time "Annots: make qleqs" (qleqs_of_qs ts sm consts ps) qs 
  else Q2S.empty

let create ts sm ps consts assm qs bm =
 {  m     = bm
  ; assm  = assm
  ; qm    = qs |>: Misc.pad_fst Q.name_of_t |> SM.of_list
  ; qleqs = Misc.with_ref_at Constants.strictsortcheck false 
              (fun () -> create_qleqs ts sm consts ps qs) 
  ; tpc   = TP.create ts sm ps consts
  
  (* Counterexamples *) 
  ; step     = 0
  ; ctrace   = IM.empty
  ; lifespan = SM.empty

  (* Stats *)
  ; stat_simple_refines = ref 0
  ; stat_tp_refines     = ref 0; stat_imp_queries    = ref 0
  ; stat_valid_queries  = ref 0; stat_matches        = ref 0
  ; stat_umatches       = ref 0; stat_unsatLHS       = ref 0
  ; stat_emptyRHS       = ref 0
  } 

(* RJ: DO NOT DELETE! *)
let ppBinding (k, zs) = 
  F.printf "ppBind %a := %a \n" 
    Sy.print k 
    (Misc.pprint_many false "," Q.print) zs

(* Take in a solution of things that are known to be true, kf. Using
   this, we can prune qualifiers whose negations are implied by
   information in kf *)
let update_pruned ks me fqm =
  List.fold_left begin fun m k ->
    if not (SM.mem k fqm) then m else
      let false_qs = SM.safeFind k fqm "update_pruned 1" in
      let qs = SM.safeFind k m "update_pruned 2" 
               |> List.filter (fun q -> (not (List.mem (k,q) false_qs))) 
      in SM.add k qs m
  end me.m ks

let apply_facts_c kf me c =
  let env = C.senv_of_t c in
  let (vv, t, lras) = C.lhs_of_t c in
  let (_,_,ras) as rhs = C.rhs_of_t c in
  let ks = rhs |> C.kvars_of_reft |> List.map snd in
  let lps = C.preds_of_lhs kf c in (* Use the known facts here *)
  let rcs = (Misc.flap (rhs_cands me)) ras in
    if rcs = [] then               (* Nothing on the right hand side *)
      me
    else if check_tp me env vv t lps [(0, A.pFalse)] = [0] then
      me
    else
      let rcs = List.filter (fun (_,p) -> not (P.is_contra p)) rcs
                |> List.map (fun (x,p) -> (x, A.pNot p)) in
	(* can we prove anything on lhs implies something on rhs is false? *)
      let fqs = BS.time "apply_facts tp" (check_tp me env vv t lps) rcs in
      let fqm = fqs |> Misc.kgroupby fst |> SM.of_list in
	  {me with m = BS.time "update pruned" (update_pruned ks me) fqm}

let apply_facts cs kf me =
  let numqs = me.m |> Ast.Symbol.SMap.to_list
              |> List.map snd |> List.concat |> List.length in
  let sol   = List.fold_left (apply_facts_c kf) me cs in
  let numqs' = sol.m |> Ast.Symbol.SMap.to_list
               |> List.map snd |> List.concat |> List.length in
  let _ = Printf.printf "Started with %d, proved %d false\n" numqs (numqs-numqs') in
    sol

let binds_of_quals ws qs =
  qs
  (* |> Q.normalize *)
  >> (fun qs -> Co.logPrintf "Using Quals: \n%a" (Misc.pprint_many true "\n" Q.print) qs; flush !Co.logChannel)
  >> (fun _ -> print_now "\nBEGIN: Qualifier Instantiation\n")
  |> BS.time "Qual Inst" (inst ws) 
  >> (fun _ -> print_now "\nDONE: Qualifier Instantiation\n")
  (* >> List.iter ppBinding *)
  |> SM.of_list 
  (* >> (fun _ -> print_now "\nDONE: QINST sm_of_list \n") *)

let binds_of_quals ws qs = 
  match !Constants.dump_simp with
  | "" -> binds_of_quals ws qs  (* regular solving mode *)
  | _  -> SM.empty              (* constraint simplification mode *)

(*
let refine_sort cs me = 
  if !Constants.refine_sort then 
    (* List.fold_left refine_sort me cs -- STACKOVERFLOW!!! *)
    let mer = ref me in
    let csr = ref cs in
    while not (!csr = []) do 
      let (c :: cs') = !csr in
      mer := refine_sort !mer c;
      csr := cs'
    done;
    !mer
  else me
*)

(* API *)
let create c facts = 
  binds_of_quals c.Cg.ws c.Cg.qs
(*  >> (fun _ -> assertf "DIED in predAbs.create 0")  *)
  |> SM.extendWith (fun _ -> (++)) c.Cg.bm
  |> create c.Cg.ts c.Cg.uops c.Cg.ps c.Cg.cons c.Cg.assm c.Cg.qs
  (* |> refine_sort c.Cg.cs *)
  |> ((!Constants.refine_sort) <?> Misc.flip (List.fold_left refine_sort) c.Cg.cs)
  |> Misc.maybe_apply (apply_facts c.Cg.cs) facts




(* API *)
let empty = create Cg.empty None

(* API *)
let meet me you = {me with m = SM.extendWith (fun _ -> (++)) me.m you.m} 

(************************************************************************)
(****************** Counterexample Generation ***************************)
(************************************************************************)

 
let ctr_examples me cs ucs = 
  let cx = Cx.create (read me) cs me.ctrace me.lifespan me.tpc in 
  List.map (Cx.explain cx) ucs


(*******************************************************************************)
(******************************** Profile/Stats ********************************)
(*******************************************************************************)

let print_m ppf s = 
  SM.iter begin fun k ds ->
    ds |> (<?>) (!Co.minquals) (min_binds s)
       |> F.fprintf ppf "solution: %a := [%a] \n\n"  Sy.print k pprint_ds 
  end s.m 
 
let print_qs ppf s = 
  SM.range s.qm
  >> (fun _ -> F.fprintf ppf "//QUALIFIERS \n\n")
  |> F.fprintf ppf "%a" (Misc.pprint_many true "\n" Q.print)
(*  |> List.iter (F.fprintf ppf "%a" Q.print) 
 *) |> ignore

(* API *)
let print ppf s = s >> print_m ppf >> print_qs ppf |> ignore

     
let botInt qs = if List.exists (Q.pred_of_t <+> P.is_contra) qs then 1 else 0

(* API *)
let print_stats ppf me =
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) me.m 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) me.m min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) me.m max_int,
     SM.fold (fun _ qs x -> x + botInt qs) me.m 0) in
  let n   = SM.length me.m in
  let avg = (float_of_int sum) /. (float_of_int n) in
  F.fprintf ppf "# Vars: (Total=%d, False=%d) Quals: (Total=%d, Avg=%f, Max=%d, Min=%d)\n" 
    n bot sum avg max min;
  F.fprintf ppf "#Iteration Profile = (si=%d tp=%d unsatLHS=%d emptyRHS=%d) \n"
    !(me.stat_simple_refines) !(me.stat_tp_refines)
    !(me.stat_unsatLHS) !(me.stat_emptyRHS);
  F.fprintf ppf "#Queries: umatch=%d, match=%d, ask=%d, valid=%d\n" 
    !(me.stat_umatches) !(me.stat_matches) !(me.stat_imp_queries)
    !(me.stat_valid_queries);
  F.fprintf ppf "%a" TP.print_stats me.tpc

(* API *)
let save fname s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" print s;
  close_out oc

let key_of_quals qs = 
  qs |> List.map P.to_string 
     |> List.sort compare
     |> String.concat ","

(* API *)
let mkbind = id (* Misc.flatten <+> Misc.sort_and_compact *)

(* API *)
let dump s = 
  s.m 
  |> SM.to_list 
  |> List.map (snd <+> List.map Q.pred_of_t)
  |> Misc.groupby key_of_quals
  |> List.map begin function 
     | [] -> assertf "impossible" 
     | (ps::_ as pss) -> Co.cprintf Co.ol_solve 
                         "SolnCluster: preds %d = size %d \n"
                         (List.length ps) (List.length pss)
     end
  |> ignore


