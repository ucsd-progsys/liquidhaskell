{-@ LIQUID "--no-termination" @-}

module Intervals where

type Offset = Int

-- | Invariant: Intervals are non-empty
{-@ data Interval = I
      { from :: Int
      , to   :: {v: Int | from < v }
      }
  @-}
data Interval  = I { from :: Offset, to :: Offset }

-- | Invariant: Intervals are sorted, disjoint and non-adjacent
{-@ type OrdIntervals N = [{v:Interval | N <= from v}]<{\fld v -> (to fld <= from v)}> @-}
type OrdIntervals = [Interval]

-- | Invariant: Intervals start with lower-bound of 0
{-@ data Intervals = Intervals { itvs :: OrdIntervals 0 } @-}
data Intervals = Intervals {itvs :: OrdIntervals }

-- | Invariant as a Haskell Predicate
{-@ okIntervals :: lb:Nat -> is:OrdIntervals lb -> {v : Bool | v } / [len is] @-}
okIntervals :: Int -> OrdIntervals -> Bool
okIntervals _ []            = True
okIntervals lb ((I f t) : is) = lb <= f && f < t && okIntervals t is

--------------------------------------------------------------------------------
-- | Unit tests
--------------------------------------------------------------------------------
okItv  = I 10 20
badItv = I 20 10

okItvs  = Intervals [I 10 20, I 30 40, I 40 50]
badItvs = Intervals [I 10 20, I 40 50, I 30 40]

--------------------------------------------------------------------------------
-- | Intersection
--------------------------------------------------------------------------------
intersect :: Intervals -> Intervals -> Intervals
intersect (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {- AUTO! go :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb -> OrdIntervals lb @-}
    go :: Int -> OrdIntervals -> OrdIntervals -> OrdIntervals
    go _ _ [] = []
    go _ [] _ = []
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2   = go lb (i2:is2) (i1:is1)
      -- disjoint
      | f1 >= f2  = go lb (i1:is1) is2
      -- subset
      | t1 == t2  = I f' t2 : go t2 is1 is2
      -- overlapping
      | otherwise = I f' t2 : go t2 ((I t2 t1) : is1) is2
      where
        f'        = max f1 f2

--------------------------------------------------------------------------------
-- | Union
--------------------------------------------------------------------------------
union :: Intervals -> Intervals -> Intervals
union (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {- AUTO! go :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb -> OrdIntervals lb @-}
    go _ is [] = is
    go _ [] is = is
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2 = go lb (i2:is2) (i1:is1)
      -- disjoint
      | f1 > t2 = i2 : go t2 (i1:is1) is2
      -- overlapping
      | otherwise  = go lb (i1 { from = f'} : is1) is2
      where f' = min (from i1) (from i2)

--------------------------------------------------------------------------------
-- | Difference
--------------------------------------------------------------------------------
subtract :: Intervals -> Intervals -> Intervals
subtract (Intervals is1) (Intervals is2) = Intervals (go 0 is1 is2)
  where
    {- AUTO! go :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb -> OrdIntervals lb @-}
    go _ is [] = is
    go _ [] _  = []
    go lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- i2 past i1
      | t1 <= f2 = i1 : go t1 is1 (i2:is2)
      -- i1 past i2
      | t2 <= f1 = go lb (i1:is1) is2
      -- i1 contained in i2
      | f2 <= f1 , t1 <= t2 = go lb is1 (i2:is2)
      -- i2 covers beginning of i1
      | f1 >= f2 = go t2 (i1 { from = t2} : is1) is2
      -- i2 covers end of i1
      | t1 <= t2 = i1 { to = f2 } : go f2 is1 (i2:is2)
      -- i2 in the middle of i1
      | otherwise = I f1 f2 : go f2 (I t2 t1 : is1) is2
