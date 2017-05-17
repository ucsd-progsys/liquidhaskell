-- From Data.ByteString.Fusion

-- Compare with tests/pos/StrictPair1.hs

module SPair (
    PairS(..)
  , moo
  -- FIX: , psnd
  ) where

import Language.Haskell.Liquid.Prelude (liquidAssert)

infixl 2 :*:

-- | Strict pair
--   But removing the strictness annotation does not change the fact that
--   this program is marked as SAFE...
data PairS a b = !a :*: !b deriving (Eq,Ord,Show)

{-@ data PairS a b <p :: x0:a -> b -> Bool> = (:*:) { spX ::a, spY ::b<p spX> }  @-}

{-@ measure psnd @-}
psnd :: PairS a b -> b
psnd ((:*:) x y) = y


{-@ type FooS a = PairS <{\z v -> v <= psnd z}> (PairS a Int) Int @-}

{-@ moo :: (FooS a) -> () @-}
moo :: PairS (PairS a Int) Int -> ()
moo (x :*: n :*: m) = liquidAssert (m <= n) ()
