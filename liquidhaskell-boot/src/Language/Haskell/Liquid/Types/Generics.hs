{- | Deriving instances of Hashable and Binary, generically.

-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Types.Generics() where

import GHC.Generics
import Data.Hashable
import Data.Binary
import Data.Hashable.Generic
import Data.Function

-- * 'Hashable'

instance (Eq (Generically a), Generic a, GHashable Zero (Rep a)) => Hashable (Generically a) where
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
