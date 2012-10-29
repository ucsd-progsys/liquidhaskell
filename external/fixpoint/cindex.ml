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
module H  = Hashtbl
module F  = Format
module BS = BNstats
module Co = Constants
module C  = FixConstraint
module Misc = FixMisc 
module IM = Misc.IntMap
module IS = Misc.IntSet
module SM = Ast.Symbol.SMap 
module SS = Ast.Symbol.SSet
module P  = Ast.Predicate

open Misc.Ops

let mydebug = false 

(* TODO: Describe the SCC ordering scheme! *)

(***********************************************************************)
(***************** Index Data Structures and Accessors *****************)
(***********************************************************************)

type rank = {
    id    : C.id
  ; scc   : int    (* SCC number with ALL dependencies    *)
  ; iscc  : int    (* SCC number without CUT dependencies *)
  ; simpl : bool   (* Is the RHS simple ?                 *)
  ; cut   : bool   (* Is the RHS a CUT-VAR                *)
  ; tag   : C.tag;
}

let string_of_tag t = 
  Printf.sprintf "[%s]" (Misc.map_to_string string_of_int t)

let pprint_rank ppf r = 
  Format.fprintf ppf "id=%d, scc=%d, iscc=%d, cut=%b, tag=%a" 
    r.id r.scc r.iscc r.cut C.print_tag r.tag

module WH = 
  Heaps.Functional (struct 
    type t = int * rank 
    let compare (ts,r) (ts',r') = 
      if r.scc <> r'.scc then compare r.scc r'.scc else
        if ts <> ts' then - (compare ts ts') else 
          if r.iscc <> r'.iscc then compare r.iscc r'.iscc else
            if !Constants.ptag && r.tag <> r'.tag then compare r.tag r'.tag else
              compare r.simpl r'.simpl
  end)

type wkl = WH.t

type t = 
  { cnst  : FixConstraint.t IM.t     (* id   -> refinement_constraint *) 
  ; rnkm  : rank IM.t                (* id   -> dependency rank *)
  ; depm  : C.id list IM.t           (* id   -> successor ids *)
  ; pend  : (C.id, unit) H.t         (* id   -> is in wkl ? *)
  ; rts   : IS.t                     (* {rank} members are "root" sccs *)
  ; ds    : C.dep list               (* add/del dep list *)
  ; rdeps : (int * int) list         (* real dependencies *)  
  ; kuts  : Ast.Symbol.t list        (* CUT KVars *)
  }

let get_ref_rank me c =
  Misc.do_catch "ERROR: Cindex.get_ref_rank" (IM.find (C.id_of_t c)) me.rnkm

let get_ref_constraint me i = 
  Misc.do_catch "ERROR: Cindex.get_ref_constraint" (IM.find i) me.cnst

(***********************************************************************)
(******************** Building Real Dependencies ***********************)
(***********************************************************************)

let refa_ko = function C.Kvar (_,k) -> Some k | _ -> None

let reft_ks = function (_,_,ras) -> Misc.map_partial refa_ko ras

let lhs_ks c = 
  c |> C.lhs_of_t
    |> reft_ks 
    |> SM.fold (fun _ (r:C.reft) l -> (reft_ks r) ++ l) (C.env_of_t c)

let rhs_ks c =
  c |> C.rhs_of_t |> reft_ks 

let make_kread_map cm = 
  cm |> IM.to_list 
     |> Misc.flap (fun (id, c) -> lhs_ks c |>: (fun k -> (k, id)))
     |> SM.of_alist 
(*     >> SM.iter (fun k ids -> Co.bprintf mydebug "ReadIn %a := %a\n" Ast.Symbol.print k Misc.pprint_pretty_ints ids) 
 *)

let make_deps cm = 
  let km = make_kread_map cm in
  cm |> IM.to_list
     |> Misc.flap (fun (id, c) -> rhs_ks c |> Misc.flap (fun k -> SM.finds k km |>: (fun id' -> (id, id'))))
     |> Misc.pad_fst IM.of_alist 
(*      >> (fst <+> IM.iter (fun i js -> Co.bprintf mydebug "DepsOf (id = %d) = @[%a@]\n" i Misc.pprint_pretty_ints js)) 
*)

(* IM.fold begin fun id c acc ->
    List.fold_left begin fun (dm, deps) k -> 
      let rd_ids = SM.finds k km in
      let deps'  = List.map (fun rd_id -> (id, rd_id)) rd_ids in
      (IM.adds id rd_ids dm, (deps' ++ deps)) 
    end acc (rhs_ks c) 
   end cm (IM.empty, [])
 *)

(***********************************************************************)
(************* Adjusting Dependencies with Provided Tag-Deps ***********)
(***********************************************************************)

let delete_deps cm dds = 
  let delf = C.matches_deps dds in
  let tagf = fun x -> IM.find x cm |> C.tag_of_t in
  List.filter (not <.> delf <.> Misc.map_pair tagf)
  
let add_deps cm ads ijs = 
  let tt = H.create 37 in
  let _  = IM.iter (fun id c -> H.add tt (C.tag_of_t c) id) cm in
  ads |> Misc.map C.tags_of_dep
      |> Misc.map (Misc.map_pair (H.find_all tt))
      |> Misc.flap (Misc.uncurry Misc.cross_product)
      |> (++) ijs

let adjust_deps cm ds = 
  let ads, dds = List.partition C.pol_of_dep ds in
  !Constants.adjdeps <?> (add_deps cm ads <.> delete_deps cm dds)

(***********************************************************************)
(**************************** Dependency SCCs **************************)
(***********************************************************************)

let string_of_ints is = is |> List.map string_of_int |> String.concat ", "

let print_rank_groups f rs = 
  rs |>  Misc.kgroupby f 
     |>  List.sort compare 
     |>  List.iter begin fun (g, rs) ->
            Format.printf "Group=%s size=%d ids=%s\n" 
              g (List.length rs) (string_of_ints (List.map (fun r -> r.id) rs)) 
          end

let string_of_cid cm id = 
  try 
    IM.find id cm 
    |> C.tag_of_t
    |> Misc.fsprintf C.print_tag
    |> Printf.sprintf "%d: %s" id 
  with _ -> assertf "string_of_cid: impossible" 

let make_rankm cm ranks iranks = 
  let rm  = IM.of_list ranks  in
  let irm = IM.of_list iranks in
  IM.domain cm 
    |>: begin fun id ->
          let c         = IM.find id cm  in
          let r         = IM.find id rm  in
          let (ir, cut) = IM.find id irm in
          id, { id    = id; scc   = r; iscc  = ir; cut   = cut; tag   = C.tag_of_t c 
              ; simpl = (not !Co.psimple) || (C.is_simple c)                         }
        end
    |> IM.of_list
    (* >> (IM.range <+> print_rank_groups (fun r -> Printf.sprintf "(%d/%d)" r.scc r.iscc ))   *)

(* returns a predicate which is true of ids whose RHS kvar is a kut-var *)
let is_cut_cst cm kuts = 
  let id_cstr     = fun i -> IM.find i cm    in
  let is_cut_kvar = let ks = SS.of_list kuts in 
                    fun k -> SS.mem k ks  
  in List.exists is_cut_kvar <.> List.map snd <.> C.kvars_of_reft <.> C.rhs_of_t <.> id_cstr 

let inner_ranks cm deps irs = function 
  | [] ->   (* if no kuts specified, use dummys *)
      irs  |>: (fun (i, r) -> (i, (r, false)))  
  | kuts -> (* else, redo the SCC computation without cut-dependencies *)
      let is_eq_rank = let rm = IM.of_list irs in  fun i j -> (IM.find i rm = IM.find j rm)  in
      let is_cut_id  = is_cut_cst cm kuts                                                    in
      let is_cut_dep = fun (i, j) -> is_cut_id i && is_eq_rank i j                           in
      deps |> List.filter (not <.> is_cut_dep)
           |> Fcommon.scc_rank "inner" (string_of_cid cm) (IM.domain cm)  
           |>: (fun (i, ir) -> (i, (ir, is_cut_id i)))

let make_ranks cm deps kuts =
  let ranks  = Fcommon.scc_rank "constraint" (string_of_cid cm) (IM.domain cm) deps in
  let iranks = inner_ranks cm deps ranks kuts                                       in
  make_rankm cm ranks iranks

let make_roots rankm ijs =
  let sccs = rankm |> IM.to_list |> Misc.map (fun (_,r) -> r.scc) in 
  let sccm = List.fold_left (fun is scc -> IS.add scc is) IS.empty sccs in
  List.fold_left begin fun sccm (i,j) ->
    let ir = (IM.find i rankm).scc in
    let jr = (IM.find j rankm).scc in
    if ir <> jr then IS.remove jr sccm else sccm
  end sccm ijs


(* A constraint c is non-live if its rhs is a k variable that is not
 * (transitively) read. 
 * roots := { c | (rhs_of_t c) has a concrete predicate }
 * lives := Pre*(roots) where Pre* is refl-trans-clos of the depends-on relation *)

let make_lives cm real_deps =
  let dm = real_deps |>: Misc.swap |> IM.of_alist in
  let js = cm |> IM.filter (fun _ -> C.is_conc_rhs) |> IM.domain |> IS.of_list  in
  (js, IS.empty)
  |> Misc.fixpoint begin fun (js, vm) ->
       let vm = IS.fold (fun j vm -> IS.add j vm) js vm in
       let js = IS.fold begin fun j js ->
                  IM.finds j dm 
                  |> List.filter (fun j -> not (IS.mem j vm)) 
                  |> IS.of_list
                  |> IS.union js
                end js IS.empty
       in ((js, vm), not (IS.is_empty js))
     end
  |> (fst <+> snd) 
  >> (IS.cardinal <+> Printf.printf "#Live Constraints: %d \n") 

let create_raw kuts ds cm dm real_deps =
  let deps = adjust_deps cm ds real_deps in
  let rnkm = make_ranks cm deps kuts     in
  { cnst = cm; ds  = ds; kuts = kuts; rdeps = real_deps; rnkm  = rnkm
  ; depm = dm; rts = make_roots rnkm deps ;  pend = H.create 17}


(***********************************************************************)
(**************************** API **************************************)
(***********************************************************************)

(* API *) 
let print ppf me =
  List.iter (Format.fprintf ppf "@[%a@] \n" C.print_dep) me.ds; 
  IM.iter (fun _ c -> Format.fprintf ppf "@[%a@] \n" (C.print_t None) c) me.cnst
 
let save fname me = 
  Misc.with_out_file fname begin fun oc -> 
    let ppf = F.formatter_of_out_channel oc in 
    F.fprintf ppf "//Sliced Constraints@.";
    F.fprintf ppf "@[%a@] \n" print me
  end

(* The "adjusted" dependencies are used to create the SCC ranks ONLY.
 * For soundness, the "real" dependencies must be used to push 
 * "successors" into the worklist. *)

(* API *)
let create kuts ds cs =
  let cm            = cs |>: (Misc.pad_fst C.id_of_t) |> IM.of_list in 
  let dm, real_deps = make_deps cm in
  create_raw kuts ds cm dm real_deps 

(* API *)
let slice me = 
  let lives = make_lives me.cnst me.rdeps in
  let cm    = me.cnst  
              |> IM.filter (fun i _ -> IS.mem i lives) in
  let dm    = me.depm  
              |> IM.filter (fun i _ -> IS.mem i lives) 
              |> IM.map (List.filter (fun j -> IS.mem j lives)) in
  let rdeps = me.rdeps 
              |> Misc.filter (fun (i,j) -> IS.mem i lives && IS.mem j lives) in  
  create_raw me.kuts me.ds cm dm rdeps
  >> save !Co.save_file

(* API *) 
let slice_wf me ws = 
  let ks = me.cnst 
           |> IM.range 
           |> Misc.flap C.kvars_of_t 
           |> Misc.map snd 
           |> SS.of_list 
  in Misc.filter (C.reft_of_wf <+> C.kvars_of_reft <+> List.exists (fun (_,k) -> SS.mem k ks)) ws
  
  
let pp_cstr_id ppf c   = F.fprintf ppf "%d" (C.id_of_t c)
let pp_cstr_ids ppf cs = F.fprintf ppf "@[%a@.@]" (Misc.pprint_many false "," pp_cstr_id) cs

(* API *) 
let deps me c =
  (try IM.find (C.id_of_t c) me.depm with Not_found -> [])
  |> List.map (get_ref_constraint me)
  (* >> (List.map C.id_of_t <+> Co.logPrintf "Deps %d = [%a]\n" (C.id_of_t c) Misc.pprint_pretty_ints) *)

(* API *)
let to_list me = IM.range me.cnst

(* 
(* API *)
let to_live_list me =
  me.cnst |> IM.to_list 
          |> Misc.map_partial (fun (i,c) -> if IS.mem i me.livs then Some c else None)

*)

let sort_iter_ref_constraints me f = 
  me.rnkm |> IM.to_list
          |> List.sort (fun (_,r) (_,r') -> compare r.tag r'.tag) 
          |> List.iter (fun (id,_) -> f (IM.find id me.cnst)) 

(* API *)
let wpush =
  let timestamp = ref 0 in
  fun me w cs ->
    incr timestamp;
    List.fold_left begin fun w c -> 
      let id = C.id_of_t c in
      if Hashtbl.mem me.pend id then w else begin 
        Co.cprintf Co.ol_solve "Pushing %d at %d \n" id !timestamp; 
        Hashtbl.replace me.pend id (); 
        WH.add (!timestamp, get_ref_rank me c) w
      end
    end w cs

let wstring w = 
  WH.fold (fun (_,r) acc -> r.id :: acc) w [] 
  |> List.sort compare
  |> Misc.map_to_string string_of_int

(* API *)
let wpop me w =
  try 
    let _, r = WH.maximum w in
    let _    = Hashtbl.remove me.pend r.id in
    let c    = get_ref_constraint me r.id in
    let _    = Co.cprintf Co.ol_solve "popping (%a) " pprint_rank r in
    let _    = Co.cprintf Co.ol_solve "from wkl = %s \n" (wstring w) in 
    (Some c, WH.remove w)
  with Heaps.EmptyHeap -> (None, w) 

let roots me =
  IM.fold begin fun id r sccm ->
   (*  if not (IM.mem r.scc me.rts) then sccm else *)
      let rs = try IM.find r.scc sccm with Not_found -> [] in
      IM.add r.scc (r::rs) sccm
  end me.rnkm IM.empty
  |> IM.map (List.hd <.> List.sort compare)
  |> IM.to_list
  |> Misc.map (fun (_,r) -> get_ref_constraint me r.id) 

(* API *)
let winit me = 
  roots me |> wpush me WH.empty  



(***************************************************************)
(*********** A Operations for Constraint Cones *****************)
(***************************************************************)

let rec cone_height = function
  | Ast.Cone.Empty    -> 
      0
  | Ast.Cone.Cone xcs -> 
      xcs |> List.map (snd <+> cone_height <+> (+) 1) |> Misc.list_max 0

let rec cone_size = function
  | Ast.Cone.Empty    ->
      0
  | Ast.Cone.Cone xcs -> 
      let ns = List.map (snd <+> cone_size) xcs in
      List.fold_left (+) (List.length ns) ns

let cone (cm, dm) =
  let rec go seen cid = 
    if IS.mem cid seen then Ast.Cone.Empty else
      let seen' = IS.add cid seen in
      match IM.finds cid dm with
      | []    -> Ast.Cone.Empty
      | cids' -> Ast.Cone.Cone (List.map (Misc.pad_snd (go seen')) cids')
  in begin fun id -> 
           (Ast.Cone.Cone [(id, go IS.empty id)])
        |> (Ast.Cone.map (fun i -> C.tag_of_t <| IM.safeFind i cm "Cindex.cone")) 
        >> (fun c -> Format.printf "CONE: %d size=%d height=%d" id (cone_size c) (cone_height c))
     end

let data_sliced_deps cs = 
  let cs = FixSimplify.WeakFixpoint.simplify_ts cs          in
  let cm = cs |>: Misc.pad_fst C.id_of_t |>  IM.of_list     in
  let dm = make_deps cm |> snd |>: Misc.swap |> IM.of_alist in
  (cm, dm)
  
(* API *)
let data_cones cs = cs |> data_sliced_deps |> cone
