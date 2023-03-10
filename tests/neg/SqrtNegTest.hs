{-@ LIQUID "--expect-error-containing=SqrtNegTest.hs:5:1" @-}
module SqrtNegTest where

test :: Floating a => a
test = sqrt (-3)
