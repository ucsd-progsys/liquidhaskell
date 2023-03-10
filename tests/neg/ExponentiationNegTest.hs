{-@ LIQUID "--expect-error-containing=ExponentiationNegTest.hs:5:1" @-}
module ExponentiationNegTest where

test :: Floating a => a
test = 0 ** (-1)
