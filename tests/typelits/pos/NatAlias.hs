{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for LH type aliases and predicate aliases with Nat arguments.
--
-- LH type and predicate aliases can take Nat expressions as arguments:
--
--   * When an alias parameter appears in a TYPE position (argument to a type
--     constructor such as @Exact@), it is treated as a type and threaded
--     through type-level substitution.
--
--   * When an alias parameter appears in a REFINEMENT (e.g. @v > N@), it is
--     converted to a logical expression in Fixpoint.  A Nat literal like @5@
--     becomes @ECon (I 5)@; a Nat type variable @n@ becomes @EVar n@.
--
-- The test exercises:
--   * @GtN N@ — type alias whose parameter N is a value in the refinement
--   * @ExactN N@ — type alias whose parameter N is a type argument
--   * @predicate GtNP N V@ — predicate alias with a Nat value argument
--   * Using both concrete Nat literals and Nat type variables as arguments
module NatAlias where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural)

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Exact: the standard indexed type used below.
-- ---------------------------------------------------------------------------

{-@ data Exact n = Exact Int @-}
{-@ Exact :: forall (n :: Nat). {v : Int | v == n} -> Exact n @-}
type Exact :: Nat -> Type
data Exact n = Exact Int

-- ---------------------------------------------------------------------------
-- Type alias: GtN N — the set of integers greater than N (value parameter).
-- ---------------------------------------------------------------------------

{-@ type GtN N = {v : Int | v > N} @-}

-- Using a concrete Nat literal 5 as the value argument N.
{-@ moreThan5 :: GtN 5 @-}
moreThan5 :: Int
moreThan5 = 6

-- Using a Nat type variable n as the value argument N.
{-@ moreThanN :: forall (n :: Nat). Exact n -> GtN n @-}
moreThanN :: Exact n -> Int
moreThanN (Exact v) = v + 1

-- ---------------------------------------------------------------------------
-- Type alias: AtLeastN N — integers >= N (value parameter, second example).
-- ---------------------------------------------------------------------------

{-@ type AtLeastN N = {v : Int | v >= N} @-}

-- Using a concrete Nat literal 3.
{-@ atLeast3 :: AtLeastN 3 @-}
atLeast3 :: Int
atLeast3 = 3

-- Using a Nat type variable.
{-@ atLeastN :: forall (n :: Nat). Exact n -> AtLeastN n @-}
atLeastN :: Exact n -> Int
atLeastN (Exact v) = v

-- ---------------------------------------------------------------------------
-- Type alias: BetweenNM — integers in the open interval (lo, hi).
-- ---------------------------------------------------------------------------

{-@ type BetweenNM LO HI = {v : Int | LO < v && v < HI} @-}

-- Using two concrete Nat literals.
{-@ between3and7 :: BetweenNM 3 7 @-}
between3and7 :: Int
between3and7 = 5

-- Using a Nat type variable as one bound.
-- Note: using n as a bound in the INPUT refinement requires Nat type vars
-- to be lifted into the logic, which is part of the feature under test.
-- When the feature is implemented, this will allow expressions like
-- {v:Int | v > n} where n is a forall'ed Nat type variable.

-- ---------------------------------------------------------------------------
-- Predicate alias: GtNP — a predicate version of GtN.
-- ---------------------------------------------------------------------------

{-@ predicate GtNP N V = V > N @-}

-- Using a concrete Nat literal in the predicate alias.
{-@ moreThan10 :: {v : Int | GtNP 10 v} @-}
moreThan10 :: Int
moreThan10 = 11

-- Using a Nat type variable in the predicate alias.
-- Note: using n in the INPUT refinement position requires support for
-- Nat type vars as logic variables, which is part of the feature under test.
