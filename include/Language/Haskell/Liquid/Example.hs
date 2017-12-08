{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder"     @-}

module ListExample where

import NewProofCombinators

import Prelude hiding ((++))

--------------------------------------------------------------------------------
-- | Lists
--------------------------------------------------------------------------------
{-@ data L [size] @-}
data L a = C a (L a) | N

size :: L a -> Int
{-@ measure size @-}
{-@ size :: L a -> Nat @-}
size N       = 0
size (C _ x) = 1 + size x

--------------------------------------------------------------------------------
-- | Appending Lists
--------------------------------------------------------------------------------
{-@ reflect ++ @-}
{-@ infixr  ++ @-}
(++) :: L a -> L a -> L a
N ++ ys        = ys
(C x xs) ++ ys = C x (xs ++ ys)

--------------------------------------------------------------------------------
-- | Complete Proofs
--------------------------------------------------------------------------------
{-@ leftId :: x:L a -> { x ++ N == x } @-}
leftId :: L a -> Proof
leftId N
  =   N ++ N
  === N                        -- equality `N ++ N === N` holds by unfolding `++`
  *** QED

leftId (C x xs)
  =    (C x xs) ++ N
  ===  C x (xs ++ N)           -- equality holds by unfolding `++`
  ==? C x xs     ? leftId xs   -- equality requires "certificate" `leftId xs`
  *** QED


--------------------------------------------------------------------------------
-- | Incomplete Proofs
--------------------------------------------------------------------------------

{-@ assoc :: x:L a -> y:L a -> z:L a->  { (x ++ y) ++ z = x ++ (y ++ z) } @-}
assoc :: L a -> L a -> L a -> Proof
assoc N y z
  =   ()
  *** Admit                  -- Give up. Replace with QED to see ERROR.

assoc (C a x) y z
  =  ((C a x) ++ y) ++ z
  ==! C a (x ++ (y ++ z))    -- Unsafe-eq; replace with `==.` or `===` to see error )
  === (C a x) ++ (y ++ z)
  *** QED
