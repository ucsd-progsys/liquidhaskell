{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Natural.Natural as int @-}

-- Regression test for https://github.com/ucsd-progsys/liquidhaskell/issues/2499
-- GHC inserts a coercion when converting between type synonyms for type-level
-- naturals (e.g. between `Vec (Succ n)` and `Vec (n+1)`). LH was unable to
-- propagate refinements through that uninterpreted coercion, causing a false
-- type error.

module T2499 where

import GHC.TypeNats (Nat, type (+))
import GHC.Natural  (Natural)

type Zero   = (0 :: Nat)
type Succ n = n + 1

{-@
data Vec [vlen] n a where
  Nil  :: Vec Zero a
  (:>) :: forall a n. a -> Vec n a -> Vec (Succ n) a
@-}
infixr 5 :>
data Vec (n :: Nat) a where
  Nil  :: Vec Zero a
  (:>) :: a -> Vec n a -> Vec (Succ n) a

{-@ measure vlen @-}
{-@ vlen :: Vec n a -> Nat @-}
vlen :: Vec n a -> Int
vlen Nil        = 0
vlen (_ :> xr)  = 1 + vlen xr

{-@
vscanl
  :: (b -> a -> b)
  -> b
  -> xs : Vec n a
  -> { ys : Vec (Succ n) b | vlen ys = 1 + vlen xs }
@-}
vscanl :: (b -> a -> b) -> b -> Vec n a -> Vec (n + 1) b
vscanl _ y Nil       = y :> Nil
vscanl f y (x :> xr) = y :> vscanl f (f y x) xr
