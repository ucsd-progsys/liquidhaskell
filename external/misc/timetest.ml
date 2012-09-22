(**************************************************************)
(*************** Unit Test For Time Modules *******************)
(**************************************************************)

open Misc.Ops

let rec repeat f n = if n > 0 then (f (); repeat f (n-1)) 

let pause_1_sec () = repeat (fun () -> ()) 112516096
let pause_n_sec n  = repeat pause_1_sec n

let rec sim n c b t = 
  if n > 0 then begin
    let id = "downtick "^(string_of_int n) in
    let _  = Printf.printf "%s \n" id in
    Timer.log_event t (Some id); 
    Tagtime.time ("pause",[id]) pause_n_sec b; 
    sim (n-1) c (c*b) t
  end

let sim n c b t = 
  sim n c b t; 
  Timer.log_event t None

let c = try Sys.argv.(1) |> int_of_string with _ -> 1
let _ = Timer.create "boo" 
        >> (fun t -> Tagtime.time ("sim", []) (sim 4 c 1) t)
        |> Format.printf "%a" Timer.print
let _ = Tagtime.dump "timetest.stat"
