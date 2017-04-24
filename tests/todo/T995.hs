{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Basics
  ( Peano(..)
  , toNat
  ) where

import           Prelude (Char, Int)
import qualified Prelude
import           Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- | Booleans ------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Bool = True | False @-}
data Bool = True | False

--------------------------------------------------------------------------------
-- | Peano ---------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect natEven @-}
natEven :: Peano -> Bool
natEven O         = True
natEven (S O)     = False
natEven (S (S n)) = natEven n

-- fails
{-@ test_Even4 :: { natEven (S (S (S (S O)))) == True } @-}
test_Even4 :: Proof
test_Even4 = trivial
