{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for type-level Nat arithmetic in LH specs (commit e66bef1).
--
-- @argType@ is generalised to translate type-level arithmetic expressions
-- (@+@, @-@, @*@, @Div@, @Mod@) into the corresponding Fixpoint @EBin@
-- expressions, enabling their use as type arguments and in refinements.
--
-- The polymorphic case @SumSucc (n+1)@ requires:
--   1. @checkAppTys@ to accept @RExprArg@ (commit 43496cf)
--   2. @tyCompat@ / @exprArgCompat@ to accept @RExprArg@ vs @RApp (+) [n,1]@
--   3. @argType (TyConApp (+) [n, 1])@ to return @EBin Plus n 1@
--   4. @caseEnv@ / @tyLitSubst@ to substitute @n+1@ at the pattern-match site
module NatArith where

import Data.Kind (Type)
import GHC.TypeNats (Nat, Natural, type (+), type (-), Div, Mod)

{-@ embed Natural as Int @-}

-- ---------------------------------------------------------------------------
-- Addition: SumSucc n stores a value equal to n+1.
-- ---------------------------------------------------------------------------

{-@ data SumSucc n = SumSucc Int @-}
{-@ SumSucc :: forall (n :: Nat). {v : Int | v == n + 1} -> SumSucc n @-}
type SumSucc :: Nat -> Type
data SumSucc n = SumSucc Int

-- Construction with a concrete literal: at n=0, field must equal 1.
mkSucc0 :: SumSucc 0
mkSucc0 = SumSucc 1

-- Construction at n=4: field must equal 5.
mkSucc4 :: SumSucc 4
mkSucc4 = SumSucc 5

-- Polymorphic: the type argument is the arithmetic expression (n+1).
-- After substituting n+1 for the constructor's type variable, the field
-- satisfies v == (n+1)+1 = n+2.
{-@ getSucc :: forall (n :: Nat). SumSucc (n + 1) -> {v : Int | v == n + 2} @-}
getSucc :: SumSucc (n + 1) -> Int
getSucc (SumSucc v) = v

-- ---------------------------------------------------------------------------
-- Subtraction: SubOne n stores a value equal to n-1.
-- ---------------------------------------------------------------------------

{-@ data SubOne n = SubOne Int @-}
{-@ SubOne :: forall (n :: Nat). {v : Int | v == n - 1} -> SubOne n @-}
type SubOne :: Nat -> Type
data SubOne n = SubOne Int

-- Construction at n=3: field must equal 2.
mkSubOne3 :: SubOne 3
mkSubOne3 = SubOne 2

-- Polymorphic: the type argument is (n-1); after substitution field == (n-1)-1 = n-2.
{-@ getSubOne :: forall (n :: Nat). SubOne (n - 1) -> {v : Int | v == n - 2} @-}
getSubOne :: SubOne (n - 1) -> Int
getSubOne (SubOne v) = v

-- ---------------------------------------------------------------------------
-- Multiplication: Doubled n stores a value equal to n*2.
-- The LH spec refinement @v == n * 2@ uses the Fixpoint @EBin Times@.
-- Tested only with concrete literals in the Haskell type to avoid needing
-- @type (*)@ in the import list (GHC 9.x parser treats @*@ specially).
-- ---------------------------------------------------------------------------

{-@ data Doubled n = Doubled Int @-}
{-@ Doubled :: forall (n :: Nat). {v : Int | v == n * 2} -> Doubled n @-}
type Doubled :: Nat -> Type
data Doubled n = Doubled Int

-- Construction at n=3: field must equal 6.
mkDoubled3 :: Doubled 3
mkDoubled3 = Doubled 6

-- Construction at n=0: field must equal 0.
mkDoubled0 :: Doubled 0
mkDoubled0 = Doubled 0

-- ---------------------------------------------------------------------------
-- Integer division: Halved n stores a value equal to n `div` 2.
-- ---------------------------------------------------------------------------

{-@ data Halved n = Halved Int @-}
{-@ Halved :: forall (n :: Nat). {v : Int | v * 2 == n} -> Halved n @-}
type Halved :: Nat -> Type
data Halved n = Halved Int

-- Construction at n=8: field must equal 4 (4*2 = 8).
mkHalved8 :: Halved 8
mkHalved8 = Halved 4

-- ---------------------------------------------------------------------------
-- Modulo: Modded n stores a value equal to n mod 7.
-- The LH refinement uses `mod` from Fixpoint's integer arithmetic.
-- ---------------------------------------------------------------------------

{-@ data Modded n = Modded Int @-}
{-@ Modded :: forall (n :: Nat). {v : Int | v == n mod 7} -> Modded n @-}
type Modded :: Nat -> Type
data Modded n = Modded Int

-- Construction at n=10: field must equal 3 (10 mod 7 = 3).
mkModded10 :: Modded 10
mkModded10 = Modded 3
