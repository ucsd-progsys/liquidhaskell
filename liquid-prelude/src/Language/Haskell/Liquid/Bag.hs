{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
-- {-@ LIQUID "--save" @-}

module Language.Haskell.Liquid.Bag where

import qualified Data.Map      as M

{-@ embed   Bag as Bag_t                                                @-}
--{-@ embed   Data.Map.Map a Int as Bag_t a                               @-}

{-@ measure Bag_empty :: Int -> Bag a                                   @-}
{-@ measure Bag_sng   :: a -> Int -> Bag a                              @-}
{-@ measure Bag_union :: Bag a -> Bag a -> Bag a                        @-}
{-@ measure Bag_count :: Bag a -> a -> Int                              @-}
{-@ measure bagSize   :: Bag a -> Int                                   @-}

-- if I just write measure fromList the measure definition is not imported
{-@ measure fromList :: [k] -> Bag k
      fromList ([])   = (Bag_empty 0)
      fromList (x:xs) = Bag_union (fromList xs) (Bag_sng x 1)
@-}

-- TODO newtype doesn't work because LH still expands the definition
data Bag a = Bag { toMap :: M.Map a Int } deriving Eq

{-@ assume empty :: {v:Bag k | v = Bag_empty 0} @-}
empty :: Bag k
empty = Bag M.empty

{-@ assume get :: (Ord k) => k:k -> b:Bag k -> {v:Nat | v = Bag_count b k}  @-}
get :: (Ord k) => k -> Bag k -> Int
get k b = M.findWithDefault 0 k (toMap b)

{-@ assume put :: (Ord k) => k:k -> b:Bag k -> {v:Bag k | v = Bag_union b (Bag_sng k 1)} @-}
{-@ ignore put @-}
put :: (Ord k) => k -> Bag k -> Bag k
put k b = Bag (M.insert k (1 + get k b) (toMap b))

{-@ assume union :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Bag_union m1 m2} @-}
union :: (Ord k) => Bag k -> Bag k -> Bag k
union b1 b2 = Bag (M.union (toMap b1) (toMap b2))

{-@ assume bagSize :: b:Bag k -> {i:Nat | i == bagSize b} @-}
bagSize :: Bag k -> Int
bagSize b = sum (M.elems (toMap b))

{-@ fromList :: (Ord k) => xs:[k] -> {v:Bag k | v == fromList xs } @-}
fromList :: (Ord k) => [k] -> Bag k
fromList []     = empty
fromList (x:xs) = put x (fromList xs)

{-@ thm_emp :: x:k -> xs:Bag k ->  { Language.Haskell.Liquid.Bag.empty /= put x xs }  @-}
thm_emp :: (Ord k) => k -> Bag k -> ()
thm_emp x xs = const () (get x xs)

{-@ assume thm_size :: xs:[k] ->  { bagSize (fromList xs) == len xs }  @-}
thm_size :: (Ord k) => [k] -> ()
thm_size _ = ()
