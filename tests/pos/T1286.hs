module Example where

{-@ fails :: {v:Bool | v} @-}
fails =  'a' == 'a'

{-@ ok :: {v:Bool | v} @-}
ok = "a" == "a"
