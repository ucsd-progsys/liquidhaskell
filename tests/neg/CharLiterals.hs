-- see #1286

module Example where

{-@ fails :: {v:Bool | v} @-}
fails =  'a' == 'b'

{-@ ok :: {v:Bool | v} @-}
ok = "a" == "a"
