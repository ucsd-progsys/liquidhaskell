module Language.Haskell.Liquid.Bag where

import qualified Data.Map as M

{-@ embed Map as Map_t @-}

type Bag a = M.Map a Int

empty :: Bag k
empty = M.empty

get :: (Ord k) => k -> Bag k -> Int
get k m = M.findWithDefault 0 k m

put :: (Ord k) => k -> Bag k -> Bag k
put k m = M.insert k (1 + get k m) m

union :: (Ord k) => Bag k -> Bag k -> Bag k
union m1 m2 = M.union m1 m2
