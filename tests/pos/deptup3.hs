module Deptup () where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

incr :: Int -> Int
incr x = x + 1

baz    :: Int -> Pair Int Int
baz x  = P x (incr x)

n :: Int
n           = choose 0

prop_baz    = chk (baz n) 

chk :: Pair Int Int -> Bool								
chk (P x y) = liquidAssertB (x <= y)
