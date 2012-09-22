(*
 * Copyright ? 1990-2010 The Regents of the University of California. All rights reserved. 
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

open FixMisc.Ops

type t = {
  name          : string; 
  mutable last  : float;
  mutable events: (int * string option * float) list;
}

let get_time  = fun _ -> (Unix.times ()).Unix.tms_utime

let create n = 
  let now = get_time () in
  { name   = n; 
    events = [(0, None, 0.0)];
    last   = now;
  }

let log_event t so =
  match t.events with
  | []         -> assertf "impossible" 
  | (i,_,_)::_ -> let now = get_time () in
                  t.events <- (i+1, so, now -. t.last)::t.events; 
                  t.last   <- now 

let to_events = fun t -> List.rev t.events
let to_name   = fun t -> t.name

let print_event ppf = function
  | (i, Some s, f) -> Format.fprintf ppf "<%6d, %6.3f, %s>@\n" i f s
  | (i, None  , f) -> Format.fprintf ppf "<%6d, %6.3f, *>@\n"  i f

let print ppf t = 
  Format.fprintf ppf "Timer %s :: @[%a@] \n" 
    t.name 
    (FixMisc.pprint_many false "" print_event) (to_events t) 


