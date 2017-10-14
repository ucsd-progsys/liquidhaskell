{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Induction where

import           Prelude (Char, Int, Bool(..))
import qualified Prelude

import Language.Haskell.Liquid.ProofCombinators

{-@ data Peano [toNat] @-} 
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect natPlus @-}
{-@ natPlus :: Peano -> Peano -> Peano @-}
natPlus :: Peano -> Peano -> Peano
natPlus O     n = n
natPlus (S m) n = S (natPlus m n)

{-@ reflect natMult @-}
{-@ natMult :: Peano -> Peano -> Peano @-}
natMult :: Peano -> Peano -> Peano
natMult n m = case n of
  O    -> O
  S n' -> natPlus m (natMult n' m)

{-@ theorem_plus_n_O :: n : Peano -> { n == natPlus n O } @-}
theorem_plus_n_O :: Peano -> Proof
theorem_plus_n_O O     = ( natPlus O O ) *** QED
theorem_plus_n_O (S n) = ( natPlus (S n) O
                         , theorem_plus_n_O n
                         ) *** QED

{-@ theorem_mult_0_r :: n : Peano -> { natMult n O = O } @-}
theorem_mult_0_r :: Peano -> Proof
theorem_mult_0_r O     = natMult O O *** QED
theorem_mult_0_r (S n) = ( natMult (S n) O
                         , theorem_mult_0_r n
                         , natPlus O O
                         ) *** QED

{-@ theorem_plus_n_Sm :: n : Peano -> m : Peano
  -> { S (natPlus n m) = natPlus n (S m) }
@-}
theorem_plus_n_Sm :: Peano -> Peano -> Proof
theorem_plus_n_Sm O     m = ( natPlus O m, natPlus O (S m) ) *** QED
theorem_plus_n_Sm (S n) m = ( natPlus (S n) m
                            , natPlus (S n) (S m)
                            , theorem_plus_n_Sm n m
                            ) *** QED

{-@ theorem_plus_comm :: n : Peano -> m : Peano
  -> { natPlus n m = natPlus m n }
@-}
theorem_plus_comm :: Peano -> Peano -> Proof
theorem_plus_comm O     m = ( natPlus O m, theorem_plus_n_O m ) *** QED
theorem_plus_comm (S n) m = ( natPlus (S n) m
                            , theorem_plus_comm n m
                            , theorem_plus_n_Sm m n
                            ) *** QED

{-@ theorem_plus_assoc :: n : Peano -> m : Peano -> p : Peano
  -> { natPlus n (natPlus m p) = (natPlus (natPlus n m) p) }
@-}
theorem_plus_assoc :: Peano -> Peano -> Peano -> Proof
theorem_plus_assoc O     m p = ( natPlus O (natPlus m p)
                               , natPlus O m
                               ) *** QED
theorem_plus_assoc (S n) m p = ( natPlus (S n) (natPlus m p)
                               , natPlus (S n) m
                               , natPlus (S (natPlus n m)) p
                               , theorem_plus_assoc n m p
                               ) *** QED

{-@ reflect double @-}
{-@ double :: Peano -> Peano @-}
double :: Peano -> Peano
double O     = O
double (S n) = S (S (double n))

{-@ theorem_double_plus :: n : Peano -> { double n = natPlus n n } @-}
theorem_double_plus :: Peano -> Proof
theorem_double_plus O     = ( double O, natPlus O O ) *** QED
theorem_double_plus (S n) = ( double (S n)
                            , theorem_double_plus n
                            , natPlus (S n) (S n)
                            , theorem_plus_n_Sm n n
                            ) *** QED

{-@ theorem_plus_swap :: n : Peano -> m : Peano -> p : Peano
  -> { natPlus n (natPlus m p) = natPlus m (natPlus n p) }
@-}
theorem_plus_swap :: Peano -> Peano -> Peano -> Proof
theorem_plus_swap n m p = ( theorem_plus_assoc n m p
                          , theorem_plus_comm n m
                          , theorem_plus_assoc m n p
                          ) *** QED

{-@ lemma_mult_distrib_S_n :: m : Peano -> n : Peano
  -> { natMult m (S n) = natPlus m (natMult m n) }
@-}
lemma_mult_distrib_S_n :: Peano -> Peano -> Proof
lemma_mult_distrib_S_n O     n = ( natMult O (S n)
                                 , natMult O n
                                 , natPlus O O
                                 ) *** QED
lemma_mult_distrib_S_n (S m) n = ( natMult (S m) (S n)
                                 , natPlus (S n) (natMult m (S n))
                                 , natPlus (S m) (natMult (S m) n)
                                 , natMult (S m) n
                                 , lemma_mult_distrib_S_n m n
                                 , theorem_plus_swap n m (natMult m n)
                                 ) *** QED

{-@ theorem_mult_comm :: m : Peano -> n : Peano
                      -> { natMult m n = natMult n m }
@-}
theorem_mult_comm :: Peano -> Peano -> Proof
theorem_mult_comm O     n = ( natMult O n
                            , theorem_mult_0_r n
                            ) *** QED
theorem_mult_comm (S m) n = ( natMult (S m) n
                            , theorem_mult_comm m n
                            , lemma_mult_distrib_S_n n m
                            ) *** QED
