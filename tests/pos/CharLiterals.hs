-- see #1286 
module CharLiterals where

{-@ fails :: {v:Bool | v} @-}
fails =  'a' == 'a'

{-@ ok :: {v:Bool | v} @-}
ok = "a" == "a"
