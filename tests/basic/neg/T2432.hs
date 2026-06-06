{-# LANGUAGE DeriveDataTypeable #-}
{-@ LIQUID "--expect-any-error" @-}

-- | Test that deriving Data does not introduce false into the environment,
-- which would make unsafe code pass verification (issue #2432).
module T2432 where

import Data.Data (Data)

{-@ data T = A | B  @-}
data T = A | B
  deriving (Data)

{-@ type TyA = { v : T | v == A } @-}

{-@ toInt :: TyA -> { i : Nat | i == 2 } @-}
toInt :: T -> Int
toInt A = 0
toInt _ = error ""
