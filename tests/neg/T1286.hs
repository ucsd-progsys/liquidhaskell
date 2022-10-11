{-@ LIQUID "--expect-any-error" @-}
module T1286 where

{-@ fails :: {v:Bool | v} @-}
fails =  'a' == 'b'

{-@ ok :: {v:Bool | v} @-}
ok = "a" == "a"
