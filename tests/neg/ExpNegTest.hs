{-@ LIQUID "--expect-error-containing=ExpNegTest.hs:6:1" @-}
module ExpNegTest where

{-@ test :: a -> {x:a | x <= 0} @-}
test :: Floating a => a -> a
test x = exp x
