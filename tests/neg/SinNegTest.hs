{-@ LIQUID "--expect-error-containing=SinNegTest.hs:6:1" @-}
module SinNegTest where

{-@ test :: a -> {x:a | x > 1} @-}
test :: Floating a => a -> a
test x = sin x
