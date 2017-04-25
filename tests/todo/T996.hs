{-@ LIQUID "--exact-data-con"                      @-}

module Induction where

import qualified Prelude
import           Prelude (Char, Int)
import Language.Haskell.Liquid.ProofCombinators

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

{-@ data Bool = True | False @-}
data Bool = True | False

{-@ reflect even @-}
even :: Peano -> Bool
even O         = True
even (S O)     = False
even (S (S n)) = even n

{-@ thmPlusCom :: n:Peano -> m:Peano -> { plus n m == plus m n} @-}
thmPlusCom :: Peano -> Peano -> Proof
thmPlusCom O     m = trivial
thmPlusCom (S n) m = [ thmPlusCom n m ] *** QED
