{-# LANGUAGE GADTs #-}
{-@ LIQUID "--higherorder" @-}

module FalsePositives where

import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- Common definitions
--------------------------------------------------------------------------------

-- Intentionally has no empty/base constructor (coinductive stream
-- representation without --adt).
data Stream a = (:>) a (Stream a)

infixr 5 :>

{-@ inline scons @-}
scons :: a -> Stream a -> Stream a
scons x xs = x :> xs

{-@ reflect smap @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

--------------------------------------------------------------------------------
-- 1. Unguarded mapFusion without the base case
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively,
--   Sections 1.2-1.3.
--
-- EXPECTED: REJECT (UNGUARDED RECURSIVE PROOF ON NON-WELL-FOUNDED STREAM).
--
-- Current Liquid Haskell accepts this proof by structural recursion on Stream,
-- even though Stream has no base constructor and the recursive proof call is
-- not coinductively guarded.
--------------------------------------------------------------------------------

{-@ mapFusion :: f:(b -> c)
              -> g:(a -> b)
              -> xs:Stream a
              -> {smap f (smap g xs) == smap (compose f g) xs}
  @-}
mapFusion :: (b -> c) -> (a -> b) -> Stream a -> Proof
mapFusion f g (x :> xs)
  = smap f (smap g (x :> xs))
    === smap f (g x :> smap g xs)
    === f (g x) :> smap f (smap g xs)
    ? mapFusion f g xs
    === f (g x) :> smap (compose f g) xs
    === compose f g x :> smap (compose f g) xs
    === smap (compose f g) (x :> xs)
    *** QED

--------------------------------------------------------------------------------
-- 2. Unguarded falseStream proving False
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively,
--   Section 1.3.
--
-- EXPECTED: REJECT (UNSOUND PROOF OF FALSE).
--
-- Recursively consumes the stream tail and claims to return a proof of false.
-- Current Liquid Haskell treats the stream tail as structurally decreasing
-- and accepts this inconsistent proof.
--------------------------------------------------------------------------------

{-@ falseStream :: Stream a -> {false} @-}
falseStream :: Stream a -> Proof
falseStream (_ :> xs) = falseStream xs

--------------------------------------------------------------------------------
-- 3. Vacuous mapFusion' via falseStream
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively,
--   Section 1.3.
--
-- EXPECTED: REJECT (DEPENDS ON UNSOUND falseStream).
--
-- Demonstrates that accepting falseStream allows inhabiting arbitrary proof
-- types such as map fusion without performing any proof work.
--------------------------------------------------------------------------------

{-@ mapFusion' :: f:(b -> c)
               -> g:(a -> b)
               -> xs:Stream a
               -> {smap f (smap g xs) == smap (compose f g) xs}
  @-}
mapFusion' :: (b -> c) -> (a -> b) -> Stream a -> Proof
mapFusion' _ _ xs = falseStream xs

--------------------------------------------------------------------------------
-- 4. Unguarded GADT equality witness falseProp
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively,
--   Section 3.0.
--
-- EXPECTED: REJECT (UNSOUND PROOF OF FALSE ON NON-WELL-FOUNDED GADT).
--
-- Recursively follows the EqRefl1 witness without producing a new constructor.
-- Current Liquid Haskell accepts this proof of false because EqC1 is treated
-- inductively despite having no base case.
--------------------------------------------------------------------------------

data Proposition a = EqC1 (Stream a) (Stream a)

{-@ data EqC1 a where
      EqRefl1 :: x:a
              -> xs:Stream a
              -> ys:Stream a
              -> Ix (EqC1 a) (EqC1 xs ys)
              -> Ix (EqC1 a) (EqC1 (scons x xs) (scons x ys))
  @-}
data EqC1 a where
  EqRefl1 :: a -> Stream a -> Stream a -> EqC1 a -> EqC1 a

{-@ falseProp :: xs:Stream a
              -> ys:Stream a
              -> Ix (EqC1 a) (EqC1 xs ys)
              -> {false}
  @-}
falseProp :: Stream a -> Stream a -> EqC1 a -> Proof
falseProp _ _ (EqRefl1 _ xs ys p) = falseProp xs ys p

--------------------------------------------------------------------------------
-- 5. Same-argument recursion under lazy + reflection
--
-- Sources:
--   Liquid Haskell PR #2771, "Check refinements of reflected non-terminating
--   definitions (#2301)".
--
-- EXPECTED: REJECT (VACUOUS SAME-ARGUMENT SELF-JUSTIFICATION).
--
-- A reflected lazy function calling itself on unchanged arguments can
-- vacuously justify its own impossible postcondition (FalseProof).
--------------------------------------------------------------------------------

data RepeatedList a
  = RCons a (RepeatedList a)
  | RNil

{-@ lazy rep @-}
{-@ reflect rep @-}
rep :: a -> RepeatedList a
rep x = RCons x (rep x)

{-@ type FalseProof = {v:() | false} @-}

{-@ lazy sameArgFalse @-}
{-@ reflect sameArgFalse @-}
{-@ sameArgFalse :: x:Int -> FalseProof @-}
sameArgFalse :: Int -> ()
sameArgFalse x = sameArgFalse x

--------------------------------------------------------------------------------
-- 6. Unbounded skipping in corecursion (filterStream)
--
-- Sources:
--   Danielsson (2010), Beating the Productivity Checker Using Embedded
--   Languages, Section 2.
--   Leino and Moskal (2014), Coinduction Simply.
--
-- EXPECTED: REJECT (NOT PRODUCTIVE FOR ALL INPUTS).
--
-- The recursive call in the otherwise branch is not guarded by (:>). Current
-- Liquid Haskell accepts filterStream because Stream is checked inductively,
-- even though filterStream diverges on infinite streams with no matching
-- elements.
--------------------------------------------------------------------------------

filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream p (x :> xs)
  | p x       = x :> filterStream p xs
  | otherwise = filterStream p xs

--------------------------------------------------------------------------------
-- 7. Negative recursive occurrence in a copredicate
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply.
--
-- EXPECTED: REJECT (NON-MONOTONE COPREDICATE).
--
-- The recursive occurrence appears under Boolean negation (not), so the
-- predicate operator is not monotone and greatest-fixed-point reasoning is
-- unsound. Current Liquid Haskell accepts it as an inductive function.
--------------------------------------------------------------------------------

badCopredicate :: Stream a -> Bool
badCopredicate (_ :> xs) =
  not (badCopredicate xs)
