{-@ LIQUID "--pruneunsorted" @-}

module Measures where

import Data.Set 

{-@ measure foo @-}
{-@ measure foo1 @-}

data F a = F a | E

foo1 :: F a -> Set a
foo1 (F x) = singleton x
foo1 E     = empty

foo :: F Int -> Int
foo (F x) = x + 1
foo E     = 0

-- bar = F
