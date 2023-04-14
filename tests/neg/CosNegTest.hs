{-@ LIQUID "--expect-error-containing=CosNegTest.hs:6:1" @-}
module CosNegTest where

{-@ test :: a -> {x:a | x > 1} @-}
test :: Floating a => a -> a
test x = cos x
