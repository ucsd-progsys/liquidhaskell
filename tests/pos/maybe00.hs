module Foo () where

gloop = poop True

{-@ poop :: z:a -> {v: Maybe a | fromJust(v) = z} @-}
poop z = Just z


