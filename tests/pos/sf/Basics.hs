{-@ LIQUID "--exact-data-con" @-}

module Basics (
  Bool(..),
  boolAnd, boolOr,
  Peano(..), toNat,
  natPlus, natMult
  ) where

import           Prelude (Char, Int)
import qualified Prelude

import Language.Haskell.Liquid.ProofCombinators

{-@ data Bool = True | False @-}
data Bool = True | False

{-@ reflect boolAnd @-}
{-@ boolAnd :: Bool -> Bool -> Bool @-}
boolAnd :: Bool -> Bool -> Bool
boolAnd True True = True
boolAnd _    _    = False

{-@
  theorem_boolAnd_Commutative :: a : Bool
                              -> b : Bool
                              -> { boolAnd a b = boolAnd b a }
@-}
theorem_boolAnd_Commutative :: Bool -> Bool -> Proof
theorem_boolAnd_Commutative a b = ( boolAnd a b, boolAnd b a ) *** QED

{-@ reflect boolOr @-}
{-@ boolOr :: Bool -> Bool -> Bool @-}
boolOr :: Bool -> Bool -> Bool
boolOr False False = False
boolOr _     _     = True

{-@ example_or1 :: { boolOr True True = True } @-}
example_or1 :: Proof
example_or1 = (boolOr True True) *** QED

{-@ example_or2 :: { boolOr True False = True } @-}
example_or2 :: Proof
example_or2 = (boolOr True False) *** QED

{-@ example_or3 :: { boolOr False True = True } @-}
example_or3 :: Proof
example_or3 = (boolOr False True) *** QED

{-@ example_or4 :: { boolOr False False = False } @-}
example_or4 :: Proof
example_or4 = (boolOr False False) *** QED

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect natEven @-}
{-@ natEven :: Peano -> Bool @-}
natEven :: Peano -> Bool
natEven O         = True
natEven (S O)     = False
natEven (S (S n)) = natEven n

{-@ example_Even4 :: { natEven (S (S (S (S O)))) = True } @-}
example_Even4 :: Proof
example_Even4 = ( natEven O
                , natEven (S (S O))
                , natEven (S (S (S (S O))))
                ) *** QED

{-@ example_Even5 :: { natEven (S (S (S (S (S O))))) = False } @-}
example_Even5 :: Proof
example_Even5 = ( natEven (S O)
                , natEven (S (S (S O)))
                , natEven (S (S (S (S (S O)))))
                ) *** QED

{-@ reflect natPlus @-}
{-@ natPlus :: Peano -> Peano -> Peano @-}
natPlus :: Peano -> Peano -> Peano
natPlus O     n = n
natPlus (S m) n = S (natPlus m n)

{-@
  theorem_natPlus_identity :: a : Peano
                           -> b : { Peano | a = b }
                           -> { natPlus a a = natPlus b b }
@-}
theorem_natPlus_identity :: Peano -> Peano -> Proof
theorem_natPlus_identity a b = trivial

{-@ reflect natEq @-}
{-@ natEq :: Peano -> Peano -> Bool @-}
natEq :: Peano -> Peano -> Bool
natEq O     O     = True
natEq (S m) (S n) = natEq m n
natEq _     _     = False

-- A difference between Coq and Liquid Haskell is that the latter does not have
-- the rewrite tactic. Therefore, we do not have the signature of the following
-- theorem to be
-- > (m : Peano) -> (n : Peano) -> (eqProof : m = n) -> (natEq m n = True)
-- and apply `eqProof` to rewrite m/n. Instead, the information is supplied
-- through refining `n`.

{-@
  theorem_natEq_correct :: m : Peano
                        -> n : { Peano | m = n }
                        -> { natEq m n = True }
@-}
theorem_natEq_correct :: Peano -> Peano -> Proof
theorem_natEq_correct O     O     = ( natEq O O ) *** QED
theorem_natEq_correct (S m) (S n) = ( theorem_natEq_correct m n
                                    , natEq (S m) (S n)
                                    ) *** QED

{-@ reflect natMult @-}
{-@ natMult :: Peano -> Peano -> Peano @-}
natMult :: Peano -> Peano -> Peano
natMult n m = case n of
  O    -> O
  S O  -> m
  S n' -> natPlus m (natMult n' m)

{-@
  lemma_natPlus_OPlus :: n : Peano
                      -> { natPlus O n = n }
@-}
lemma_natPlus_OPlus :: Peano -> Proof
lemma_natPlus_OPlus n = ( natPlus O n ) *** QED

{-@
  theorem_natMult_OPlus :: m : Peano
                        -> n : Peano
                        -> { natMult (natPlus O m) n = natMult m n }
@-}
theorem_natMult_OPlus :: Peano -> Peano -> Proof
theorem_natMult_OPlus m n = ( lemma_natPlus_OPlus
                            , natMult (natPlus O m) n
                            ) *** QED

{-@
  theorem_natMult_SOne :: m : Peano
                       -> n : { Peano | S n = m }
                       -> { natMult m (S n) = natMult m m }
@-}
theorem_natMult_SOne :: Peano -> Peano -> Proof
theorem_natMult_SOne m n = ( natMult m (S n) ) *** QED
