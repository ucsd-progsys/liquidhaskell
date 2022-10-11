{-@ LIQUID "--expect-error-containing=is not a subtype of the required type" @-}
{-@ LIQUID "--reflection" @-}

module IrregularData where

import Language.Haskell.Liquid.ProofCombinators (Proof, (***), QED(..), (===))

-- import Demo.Lib 

---------------------------------
-- Copy pasted from containers --
---------------------------------

data FingerTree a
    = EmptyT
    | Single a
    | Deep !(Digit a) (FingerTree (Node a)) !(Digit a)

data Node a
    = Node2 a a
    | Node3 a a a

data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a

{-@ reflect consTree @-}
consTree        :: a -> FingerTree a -> FingerTree a
consTree a EmptyT       = Single a
consTree a (Single b)   = Deep (One a) EmptyT (One b)
consTree a (Deep (Four b c d e) m sf) = Deep (Two a b) (Node3 c d e `consTree` m) sf
consTree a (Deep (Three b c d) m sf) = Deep (Four a b c d) m sf
consTree a (Deep (Two b c) m sf) = Deep (Three a b c) m sf
consTree a (Deep (One b) m sf) = Deep (Two a b) m sf

-------------------------
-- Complexity analysis --
-------------------------

{-@ phi :: FingerTree a -> Nat @-}
{-@ reflect phi @-}
phi :: FingerTree a -> Int
phi EmptyT = 0
phi (Single _) = 0
phi (Deep u q v) = dang u + phi q + dang v

{-@ dang :: Digit a -> { n:Int | n == 0 || n == 1 } @-}
{-@ reflect dang @-}
dang :: Digit a -> Int
dang One {} = 1
dang Two {} = 0
dang Three {} = 0
dang Four {} = 1

{-@ consT :: a -> FingerTree a -> Nat @-}
{-@ reflect consT @-}
consT :: a -> FingerTree a -> Int
consT _ EmptyT = 1
consT _ (Single _) = 1
consT _ (Deep One {} _ _) = 1
consT _ (Deep Two {} _ _) = 1
consT _ (Deep Three {} _ _) = 1
consT _ (Deep (Four _ a b c) q _) = 1 + consT (Node3 a b c) q

{-@ amortizedConsP :: x:a -> q:FingerTree a -> { consT x q + phi (consTree x q) - phi q <= 3 } @-}
amortizedConsP :: a -> FingerTree a -> Proof
amortizedConsP x EmptyT = consT x EmptyT + phi (consTree x EmptyT) - phi EmptyT *** QED
amortizedConsP x (Single a) =
  consT x (Single a) + phi (consTree x (Single a)) - phi (Single a)
    === 1 + phi (Deep (One x) EmptyT (One a))
    === 1 + dang (One x) + phi EmptyT + dang (One a)    -- This is the line that causes the hang/crash
    === undefined
    *** QED
amortizedConsP _ _ = undefined

