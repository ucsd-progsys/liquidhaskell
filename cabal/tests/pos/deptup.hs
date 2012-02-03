module Deptup where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

mkPair x y = P x y


incr x = x + 1

baz    :: Int -> Pair Int Int    
baz x  = mkPair x (incr x)

bazList  xs = map baz xs

n           = choose 0
xs          = [0, 1, 2, 3]

prop_baz    = map chk $ bazList xs 

chk (P x y) = assert (x <= y)


