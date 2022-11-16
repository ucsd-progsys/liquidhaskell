{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-@ embed GHC.Natural.Natural as int @-}
{-@ LIQUID "--no-totality" @-}

module T2096 where

import Prelude 
import GHC.TypeLits
import GHC.Natural
import Unsafe.Coerce

-- See https://github.com/ucsd-progsys/liquidhaskell/issues/2095
workaround :: (n1 + 1) ~ (n2 + 1) => Vec n1 a -> Vec n2 a
workaround = unsafeCoerce

data Vec (n :: Nat) a where
    Nil :: Vec 0 a
    Cons :: a -> Vec n a -> Vec (n + 1) a

foo :: Vec n a -> Vec n a -> Vec n a
foo Nil Nil = Nil
foo (Cons x xs) (Cons y ys) = Cons x zs
  where
    zs = foo xs $ workaround ys
foo _ _ = undefined

