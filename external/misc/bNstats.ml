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

                                        (* A hierarchy of timings *)
type t = { name : string;
           mutable time : float;
           mutable sub  : t list}

                                        (* Create the top level *)
let top = { name = "TOTAL";
            time = 0.0;
            sub  = []; }

                                        (* The stack of current path through 
                                         * the hierarchy. The first is the 
                                         * leaf. *)
let current : t list ref = ref [top]

let reset () = top.sub <- []

let do_time = ref true 

let dont_time () = do_time := false

let print chn msg = 
  (* Total up *)
  top.time <- List.fold_left (fun sum f -> sum +. f.time) 0.0 top.sub;
  let rec prTree ind node = 
    Printf.fprintf chn "%s%-20s          %6.3f s\n" 
      (String.make ind ' ') node.name node.time  ;
    List.iter (prTree (ind + 2)) node.sub
  in
  Printf.fprintf chn "%s" msg;
  List.iter (prTree 0) [ top ]
        
let time str f arg = 
  (* Find the right stat *)
  let stat : t = 
    let curr = match !current with h :: _ -> h | _ -> assert false in
    let rec loop = function
        h :: _ when h.name = str -> h
      | _ :: rest -> loop rest
      | [] -> 
          let nw = {name = str; time = 0.0; sub = []} in
            curr.sub <- nw :: curr.sub;
            nw
    in
      loop curr.sub
  in
  let oldcurrent = !current in
    current := stat :: oldcurrent;
    let start = (Unix.times ()).Unix.tms_utime in
    let _ = if str == "interp" then Printf.printf "interp start = %6.3f\n" start in
    let res   = 
      try (f arg) with
	  x -> (let finish   = Unix.times () in
		let diff = finish.Unix.tms_utime -. start in
		let _ = if str == "interp" then Printf.printf "interp elapsed = %6.3f\n" diff in
		  stat.time <- stat.time +. (diff);
		  current := oldcurrent;
                  raise x) (* Pop the current stat *)
    in
    let finish   = Unix.times () in
    let diff = finish.Unix.tms_utime -. start in
    let _ = if str == "interp" then Printf.printf "interp elapsed = %6.3f\n" diff in
      stat.time <- stat.time +. (diff);
      current := oldcurrent;
      res
	

let time str f arg = if !do_time then time str f arg else f arg  

let print chn msg = if !do_time then print chn msg else ()
















