module CosNegTest where

{-@ test :: a -> {x:a | x > 1} @-}
test :: Floating a => a -> a
test x = cos x
