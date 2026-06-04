{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-@ LIQUID "--reflection" @-}

-- | This module tests that transitive dependencies that use
-- UNPACK pragmas do not prevent verification of the module.
--
-- In this module the type using UNPACK is
-- GHC.Internal.Stack.Types.SrcLoc
module Unpack2695 where

import Prelude hiding (head)
import GHC.TypeNats (Nat, type (+))

-- currently without the size parameter due to
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2499
{-@
data LHVec [vlen] a where
  Nil  :: LHVec a
  Cons :: forall a. a -> LHVec a -> LHVec a
@-}
data LHVec a where
  Nil  :: LHVec a
  Cons :: a -> LHVec a -> LHVec a

type Vec (n :: Nat) a = LHVec a

{-@
measure vlen
vlen :: LHVec a -> Nat
@-}
vlen :: LHVec a -> Int
vlen Nil           = 0
vlen (_ `Cons` br) = 1 + vlen br

{-@
reflect head
head :: { xs : LHVec a | vlen xs > 0 } -> a
@-}
head :: Vec (n + 1) a -> a
head (x `Cons` _) = x
head Nil = error "unreachable"

