module Foo where


moo = poo z z 
  where z       = blerg True 
        blerg True = Nothing

{-@ poo :: x:Maybe a -> {v: Maybe a | v = x } -> Bool @-}
poo :: Maybe a -> Maybe a -> Bool
poo x y = True







