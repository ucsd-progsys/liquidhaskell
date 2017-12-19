module Language.Haskell.Liquid.Bag where

import qualified Data.Map as M

{-@ embed   M.Map as Map_t                                  @-}
{-@ measure Map_default :: Int -> Bag a                     @-}
{-@ measure Map_union   :: Bag a -> Bag a -> Bag a          @-}
{-@ measure Map_select  :: M.Map k v -> k -> v              @-}
{-@ measure Map_store   :: M.Map k v -> k -> v -> M.Map k v @-}

type Bag a = M.Map a Int

{-@ assume empty :: {v:Bag k | v = Map_default 0} @-}
empty :: Bag k
empty = M.empty

{-@ assume get :: (Ord k) => k:k -> b:Bag k -> {v:Nat | v = Map_select b k}  @-}
get :: (Ord k) => k -> Bag k -> Int
get k m = M.findWithDefault 0 k m

{-@ assume put :: (Ord k) => k:k -> b:Bag k -> {v:Bag k | v = Map_store b k (1 + (Map_select b k))} @-}
put :: (Ord k) => k -> Bag k -> Bag k
put k m = M.insert k (1 + get k m) m

{-@ assume union :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Map_union m1 m2} @-}
union :: (Ord k) => Bag k -> Bag k -> Bag k
union m1 m2 = M.union m1 m2
