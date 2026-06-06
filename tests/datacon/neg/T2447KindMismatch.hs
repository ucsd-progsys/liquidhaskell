{-@ LIQUID "--expect-error-containing=Haskell type" @-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | Negative test: a Nat literal in a spec at a Symbol type parameter
-- position should be rejected as a kind mismatch.
--
-- Previously, 'exprArgCompat' treated any 'RExprArg' as a wildcard, so the
-- mismatch was silently accepted.  With kind-aware checking, the Nat
-- expression @42@ is incompatible with the Symbol-kinded sort expected by
-- 'Labeled', and LH now emits "Specified type does not refine Haskell type".

module T2447KindMismatch where

import GHC.Base    (Type)
import GHC.TypeLits (Symbol)

type Labeled :: Symbol -> Type
data Labeled s = Labeled Int

{-@ data Labeled s = Labeled Int @-}
{-@ Labeled :: forall (s :: Symbol). Int -> Labeled s @-}

-- Wrong: the spec uses the Nat literal 42 where GHC has the Symbol "hello".
-- LH must reject this with a type-mismatch error.
{-@ labeledSz :: Labeled 42 -> Int @-}
labeledSz :: Labeled "hello" -> Int
labeledSz (Labeled n) = n
