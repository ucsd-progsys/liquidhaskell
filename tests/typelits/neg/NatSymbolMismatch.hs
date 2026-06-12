{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--expect-any-error"  @-}
{-@ LIQUID "--prune-unsorted"    @-}

-- | Negative test: kind mismatch between Nat and Symbol must be rejected.
--
-- @Labeled s@ is indexed by a @Symbol@.  The function @mkBad@ has a correct
-- Haskell type (@Labeled "hello"@) but the LH spec claims @Labeled 42@,
-- using a Nat literal @42@ where a Symbol is expected.  LH should detect
-- the kind mismatch (Nat vs Symbol) and report an error.
module NatSymbolMismatch where

import GHC.TypeLits (Symbol)

{-@ data Labeled s a = Labeled a @-}
newtype Labeled (s :: Symbol) a = Labeled a

-- The LH spec uses a Nat literal (42) in a position that expects a Symbol.
-- This is a kind mismatch and should be rejected by LH.
{-@ mkBad :: Labeled 42 Int @-}
mkBad :: Labeled "hello" Int
mkBad = Labeled (0 :: Int)
