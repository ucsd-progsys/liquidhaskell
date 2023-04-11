{- | Geriving instances, generically.
   This module shares some of the underlying ideas and implementations of the
   [generic-data](https://hackage.haskell.org/package/generic-data-0.8.1.0/docs/Generic-Data.html)
   package, allowing us to derive a bunch of instances using the underlying 'Generic' implementation,
   but in a more declarative way.

   In particular we introduc the 'Generically' newtype wrapper to be used with '-XDerivingVia' to make
   derivation explicit. For example:

@
  data Foo = Foo
       deriving Generic
       deriving Eq via Generically Foo
@

-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Haskell.Liquid.Types.Generics where

import GHC.Generics
import Data.Hashable
import Data.Binary
import Data.Hashable.Generic
import Data.Function

newtype Generically a = Generically a deriving Generic

-- * 'Hashable'

instance (Generic a, GHashable Zero (Rep a)) => Hashable (Generically a) where
  hashWithSalt s (Generically a) = genericHashWithSalt s a

-- * 'Binary'

instance (Generic a, GBinaryPut (Rep a), GBinaryGet (Rep a)) => Binary (Generically a) where
  get = Generically . to' <$> gget
  put (Generically a) = gput (from' a)

-- * 'Eq'

-- | Generic @('==')@.
--
-- @
-- instance 'Eq' MyType where
--   ('==') = 'geq'
-- @
geq :: (Generic a, Eq (Rep a ())) => a -> a -> Bool
geq = (==) `on` from'

instance (Generic a, Eq (Rep a ())) => Eq (Generically a) where
  (Generically a) == (Generically b) = geq a b

-- | A helper for better type inference.
from' :: Generic a => a -> Rep a ()
from' = from

to' :: Generic a => Rep a () -> a
to' = to
