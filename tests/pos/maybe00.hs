module Foo () where

gloop = hoop True

{-@ hoop :: z:a -> {v: Maybe a | mbFromJust v == z} @-}
hoop z = Just z


