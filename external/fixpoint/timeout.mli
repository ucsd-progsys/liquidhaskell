(* simple timeout mechanism executes a function for a number of seconds
 * specified by the first argument *)

val do_timeout: int -> ('a -> 'b) -> 'a  -> 'b option
