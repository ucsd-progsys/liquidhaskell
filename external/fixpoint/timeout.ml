

module M = Mutex
module T = Thread

let get_time () = int_of_float (Unix.time ())

let mk_task =
  fun f x lk (ret, rd) -> let rv = f x in
    M.lock lk; ret := Some rv; rd := true; M.unlock lk

let not_done lk (ret, rd) = 
  M.lock lk; let trd = !rd in (M.unlock lk; not(trd))

let fail thread (ret, rd) =
  T.kill thread; ret := None; rd := true 

let do_timeout i f x =
  let task = mk_task f x in
  let (ret, rd) as rr = (ref None, ref false) in
  let stime = get_time () in
  let lk = M.create () in 
  let t  = T.create (task lk) rr in
  while not_done lk rr do
    if (get_time () - stime < i) then
      T.yield ()
    else
      fail t rr
  done; !ret

