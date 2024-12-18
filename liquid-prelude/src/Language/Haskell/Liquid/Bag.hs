{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Language.Haskell.Liquid.Bag where

import qualified Data.Map      as M

{-@ embed   Bag as Bag_t                             @-}
{-@ measure bagSize       :: Bag a -> Int            @-}

-- if I just write measure fromList the measure definition is not imported
{-@ measure fromList :: [k] -> Bag k
      fromList ([])   = (Bag_empty 0)
      fromList (x:xs) = Bag_union (fromList xs) (Bag_sng x 1)
@-}


-- TODO newtype doesn't work because LH still expands the definition
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2332
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

{-@ fromList :: (Ord k) => xs:[k] -> {v:Bag k | v == fromList xs } @-}
fromList :: (Ord k) => [k] -> Bag k
fromList []     = empty
fromList (x:xs) = put x (fromList xs)

{-@ assume union :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Bag_union m1 m2} @-}
union :: (Ord k) => Bag k -> Bag k -> Bag k
union b1 b2 = Bag (M.unionWith (+) (toMap b1) (toMap b2))

{-@ assume unionMax :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Bag_union_max m1 m2} @-}
unionMax :: (Ord k) => Bag k -> Bag k -> Bag k
unionMax b1 b2 = Bag (M.unionWith max (toMap b1) (toMap b2))

{-@ assume interMin :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Bag_inter_min m1 m2} @-}
interMin :: (Ord k) => Bag k -> Bag k -> Bag k
interMin b1 b2 = Bag (M.intersectionWith min (toMap b1) (toMap b2))

{-@ assume sub :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bool | v = Bag_sub m1 m2} @-}
sub :: (Ord k) => Bag k -> Bag k -> Bool
sub b1 b2 = M.isSubmapOfBy (<=) (toMap b1) (toMap b2)

{-@ assume bagSize :: b:Bag k -> {i:Nat | i == bagSize b} @-}
bagSize :: Bag k -> Int
bagSize b = sum (M.elems (toMap b))

{-@ thm_emp :: x:k -> xs:Bag k -> { Language.Haskell.Liquid.Bag.empty /= put x xs } @-}
thm_emp :: (Ord k) => k -> Bag k -> ()
thm_emp x xs = const () (get x xs)

{-@ assume thm_size :: xs:[k] -> { bagSize (fromList xs) == len xs } @-}
thm_size :: (Ord k) => [k] -> ()
thm_size _ = ()
