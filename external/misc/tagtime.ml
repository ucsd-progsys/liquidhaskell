(*
 *
 * Copyright (c) 2001 by
 *  George C. Necula	necula@cs.berkeley.edu
 *  Scott McPeak        smcpeak@cs.berkeley.edu
 *  Wes Weimer          weimer@cs.berkeley.edu
 *   
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software for research purposes only is hereby granted, 
 * provided that the following conditions are met: 
 * 1. XSRedistributions of source code must retain the above copyright notice, 
 * this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, 
 * this list of conditions and the following disclaimer in the documentation 
 * and/or other materials provided with the distribution. 
 * 3. The name of the authors may not be used to endorse or promote products 
 * derived from  this software without specific prior written permission. 
 *
 * DISCLAIMER:
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR 
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT, 
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, 
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS 
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON 
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF 
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

open Misc.Ops

(******************************************************************)
(************************* Definitions ****************************)
(******************************************************************)

                                        (* A hierarchy of timings *)
type t = { name : string * (string list);
           mutable time : float;
           mutable sub  : t list}

                                        (* Create the top level *)
let top = { name = "TOTAL", [];
            time = 0.0;
            sub  = []; }

                                        (* The stack of current path through 
                                         * the hierarchy. The head is the 
                                         * leaf. *)
let current : t list ref = ref [top]

let subtime x = 
  x.sub |> List.map (fun y -> y.time) 
        |> List.fold_left (+.) 0.0 

(******************************************************************)
(************************* Printing *******************************)
(******************************************************************)

let _print x chn msg = 
  x.time <- subtime x; 
  let rec prTree ind node = 
    Printf.fprintf chn "%s%-20s          %6.3f s\n" 
      (String.make ind ' ') (fst node.name) node.time  ;
    List.iter (prTree (ind + 2)) node.sub
  in Printf.fprintf chn "%s" msg; prTree 0 x
 
let collapse (x: t) : t = failwith "TBD: Tagtime.collapse"

(* API *)
let print chn msg = _print (collapse top) chn msg

(******************************************************************)
(************************* Timing *********************************)
(******************************************************************)

let restore_stat (oldcurrent, start, stat) = 
  let stop = Unix.times () in
  let diff = stop.Unix.tms_utime -. start in
  stat.time <- stat.time +. diff; 
  current := oldcurrent

let find_stat stags =
  let curr = (match !current with h :: _ -> h | _ -> assert false) in
  let rec loop = function
    | h :: _ when h.name = stags -> h
    | _ :: rest -> loop rest
    | [] -> let nw = {name = stags; time = 0.0; sub = []} in
            curr.sub <- nw :: curr.sub;
            nw
  in loop curr.sub

(* API *)
let time (str, tags) f arg = 
  let stat = find_stat (str, List.sort compare tags) in 
  let oldcurrent = !current in
  let _ = current := stat :: oldcurrent in
  let start = (Unix.times ()).Unix.tms_utime in
  try 
    let res = f arg in
    restore_stat (oldcurrent, start, stat);
    res  
  with x -> begin
    restore_stat (oldcurrent, start, stat);
    raise x
  end 

(******************************************************************)
(************************* Logging ********************************)
(******************************************************************)

let dump_to_channel chn = 
  top.time <- subtime top;
  let rec prTree tags node =
    let s, ts = node.name in
    let tags' = [s] ++ ts ++ tags in
    let time' = max 0.0 (node.time -. (subtime node)) in
    Printf.fprintf chn "%s,%6.3f\n" (String.concat "," tags') time';
    List.iter (prTree tags') node.sub
  in prTree [] top 

(* API *)
let dump = fun fn -> fn |> open_out >> dump_to_channel |> close_out
