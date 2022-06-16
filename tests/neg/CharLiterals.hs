{-@ LIQUID "--expect-any-error" @-}
-- see #1286

module CharLiterals where

{-@ fails :: {v:Bool | v} @-}
fails =  'a' == 'b'

{-@ ok :: {v:Bool | v} @-}
ok = "a" == "a"
