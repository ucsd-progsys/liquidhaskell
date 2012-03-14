module Deptup where

import Language.Haskell.Liquid.Prelude

-- data Pair a b = P a b

data Pair = P Int Int

incr :: Int -> Int
incr x = x + 1

baz    :: Int -> Pair
baz x  = P x (incr x)

bazList  xs = map baz xs

n           = choose 0


xs          = [0,1,2,3,4]

prop_baz    = chk (baz n) --map chk ( bazList xs )
--prop =  chk (P 0 1)
chk (P x y) = assert (x <= y)
