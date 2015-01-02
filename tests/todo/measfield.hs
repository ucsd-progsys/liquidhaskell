module Goo (Vec (..)) where

data Vec a = V { vsz :: Int, velems :: [a] }

{-@ data Vec a  = V { vsz :: Int, velems :: {v:[a] | len v = vsz} } @-}

{-@ foo :: x:Vec a -> {v:[a] | len v = vsz x} @-}
foo v = velems v 

{-@ bar :: x:Vec a -> {v:[a] | len v = vsz x} @-}
bar (V _ ys) = ys 
