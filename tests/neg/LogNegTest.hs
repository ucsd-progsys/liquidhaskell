{-@ LIQUID "--expect-error-containing=LogNegTest.hs:5:1" @-}
module LogNegTest where

test :: Floating a => a
test = log 0
