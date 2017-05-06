-- From Data.ByteString.Fusion

-- Compare with tests/neg/StrictPair0.hs

module SPair (
    PairS(..)
  , moo
  ) where

infixl 2 :*:

-- | Strict pair
--   But removing the strictness annotation does not change the fact that
--   this program is marked as SAFE...
data PairS a b = !a :*: !b deriving (Eq,Ord,Show)

{-@ qualif PSnd(v: a, x:b): v = (psnd x)                            @-}

{-@ data PairS a b <p :: x0:a -> b -> Bool> = (:*:) { spX ::a, spY ::b<p spX> }  @-}

{-@ measure pfst :: (PairS a b) -> a
    pfst ((:*:) x y) = x
  @-}

{-@ measure psnd :: (PairS a b) -> b
    psnd ((:*:) x y) = y
  @-}

{-@ type FooS a = PairS <{\z v -> v <= (psnd z)}> (PairS a Int) Int @-}

{-@ moo :: a -> Int -> (FooS a) @-}
moo :: a -> Int -> PairS (PairS a Int) Int
moo x n = (x :*: n :*: m)
-- moo x n = (x :*: 1 :*: 100) -- ALAS, also reported "SAFE"
  where
    m   = n + 1
