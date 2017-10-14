{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Induction where

import qualified Prelude
import           Prelude (Char, Int, Bool (..))
import Language.Haskell.Liquid.ProofCombinators

-- TODO:import Basics

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

{-@ reflect mult @-}
mult :: Peano -> Peano -> Peano
mult n m = case n of
  O    -> O
  S n' -> plus m (mult n' m)

{-@ data BBool = BTrue | BFalse @-}
data BBool = BTrue | BFalse

{-@ reflect negb @-}
negb :: BBool -> BBool
negb BTrue  = BFalse
negb BFalse = BTrue

{-@ reflect even @-}
even :: Peano -> BBool
even O         = BTrue
even (S O)     = BFalse
even (S (S n)) = even n

--------------------------------------------------------------------------------
-- | Exercise : basic_induction ------------------------------------------------
--------------------------------------------------------------------------------

{-@ thmPlusNO :: n:Peano -> { plus n O == n } @-}
thmPlusNO       :: Peano -> Proof
thmPlusNO O     = trivial
thmPlusNO (S n) = thmPlusNO n

{-@ thmMultOR :: n:Peano -> { mult n O == O } @-}
thmMultOR :: Peano -> Proof
thmMultOR O     = trivial
thmMultOR (S n) = thmMultOR n

{-@ thmPlusNSm :: n:Peano -> m:Peano -> {S (plus n m) == plus n (S m)} @-}
thmPlusNSm :: Peano -> Peano -> Proof
thmPlusNSm O     m = trivial
thmPlusNSm (S n) m = thmPlusNSm n m

{-@ thmPlusCom :: n:Peano -> m:Peano -> { plus n m == plus m n} @-}
thmPlusCom :: Peano -> Peano -> Proof
thmPlusCom O     m = thmPlusNO m
thmPlusCom (S n) m = [ thmPlusCom n m, thmPlusNSm m n ] *** QED

{-@ thmPlusAssoc :: a:Peano -> b:Peano -> c:Peano
                 -> { plus a (plus b c) = (plus (plus a b) c) } @-}
thmPlusAssoc :: Peano -> Peano -> Peano -> Proof
thmPlusAssoc O     b c = trivial
thmPlusAssoc (S a) b c = thmPlusAssoc a b c

{- NOTE:Compare the above to:

{-@ thmPlusAssoc :: a b c : Peano -> { plus a (plus b c) = (plus (plus a b) c)} @-}

  x y z : s -> t
  x:s -> y:s -> z:s -> t

Theorem plus_assoc' : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite → IHn'. reflexivity. Qed.

Coq is perfectly happy with this. For a human, however, it is difficult to make much sense of it. We can use comments and bullets to show the structure a little more clearly...

Theorem plus_assoc'' : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite → IHn'. reflexivity. Qed.

 -}

--------------------------------------------------------------------------------
-- | Exercise : double_plus ----------------------------------------------------
--------------------------------------------------------------------------------
{-@ reflect double @-}
double :: Peano -> Peano
double O     = O
double (S n) = S (S (double n))

{-@ thmDoublePlus :: n:Peano -> { double n == plus n n } @-}
thmDoublePlus :: Peano -> Proof
thmDoublePlus O     = trivial
thmDoublePlus (S n) = [ -- double (S n)
                        -- ==. S (S (double n)) ?
                        thmDoublePlus n
                        -- ==. S (S (plus n n)) ?
                      , thmPlusNSm n n
                        -- ==. S (plus n (S n))
                        -- ==. plus (S n) (S n)
                      ] *** QED

{-@ thmEvenS :: n:Peano -> { even (S n) == negb (even n) } @-}
thmEvenS :: Peano -> Proof
thmEvenS O         = trivial
thmEvenS (S O)     = trivial
thmEvenS (S (S n)) = thmEvenS n

                   -- =   negb (even (S (S n)))
                   -- ==. negb (even n)
                   -- ==. even (S n)       ? thmEvenS n
                   -- *** QED

{- NOTE: An interesting example of `trivial`: the following

       Theorem mult_0_plus' : ∀n m : nat,
         (0 + n) * m = n * m.
       Proof.
         intros n m.
         assert (H: 0 + n = n). { reflexivity. }
         rewrite → H.
         reflexivity. Qed.

   is simply trivial.

  -}

{-@ thmMultOPlus :: n:_ -> m:_ -> { mult (plus O n) m = mult n m } @-}
thmMultOPlus :: Peano -> Peano -> Proof
thmMultOPlus n m = trivial

{-@ thmPlusRearrange :: n:Peano -> m:Peano -> p:Peano -> q:Peano
                     -> { plus (plus n m) (plus p q) = plus (plus m n) (plus p q) }  @-}

thmPlusRearrange :: Peano -> Peano -> Peano -> Peano -> Proof
thmPlusRearrange n m p q = thmPlusCom n m

{-@ thmPlusSwap :: n : Peano -> m : Peano -> p : Peano
                -> { plus n (plus m p) = plus m (plus n p) }  @-}
thmPlusSwap :: Peano -> Peano -> Peano -> Proof
thmPlusSwap n m p = [ -- plus n (plus m p) ?
                      thmPlusAssoc n m p
                      -- ==. plus (plus n m) p ?
                    , thmPlusCom n m
                      -- ==. plus (plus m n) p ?
                    , thmPlusAssoc m n p
                      -- ==. plus m (plus n p)
                    ] *** QED


{-@ thmMultSR :: m:Peano -> n:Peano -> { plus m (mult m n) = mult m (S n) } @-}
thmMultSR :: Peano -> Peano -> Proof
thmMultSR O     n = trivial
thmMultSR (S m) n = [ -- plus (S m) (mult (S m) n)
                      -- ==. plus (S m) (plus n     (mult m n))
                      -- ==. plus n     (plus (S m) (mult m n))  ?
                      thmPlusSwap n (S m) (mult m n)
                      -- ==. plus n     (S (plus m  (mult m n))) ?
                    , thmPlusNSm n (plus m (mult m n))
                      -- ==. S (plus n (plus m (mult m n)))
                      -- ==. plus (S n) (plus m (mult m n))      ?
                    , thmMultSR m n
                      -- ==. plus (S n) (mult m (S n))
                      -- ==. mult (S m) (S n)
                    ] *** QED

{-@ thmMultCom :: n:Peano -> m:Peano -> { mult n m = mult m n } @-}
thmMultCom :: Peano -> Peano -> Proof
thmMultCom O     m = thmMultOR m
thmMultCom (S n) m = [ -- mult (S n) m
                       -- ==. plus m (mult n m) ?
                       thmMultCom n m
                       -- ==. plus m (mult m n) ?
                     , thmMultSR  m n
                       -- ==. mult m (S n)
                     ] *** QED
