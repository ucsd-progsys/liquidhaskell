module Deptup where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

-- mkPair x y = P x y

incr x = x + 1

-- baz    :: Int -> Pair Int Int    
-- baz x       = P x (incr x)
baz x       = P x (incr x)

bazList  xs = map baz xs

n           = choose 0
xs          = [0..n]

chk (P x y) = assert (x < y)
prop_baz    = map chk $ bazList xs 
