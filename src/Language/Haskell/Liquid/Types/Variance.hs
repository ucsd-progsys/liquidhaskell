{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}

module Language.Haskell.Liquid.Types.Variance ( Variance(..), VarianceInfo ) where

import Prelude hiding (error)
import Control.DeepSeq
import Data.Typeable
import Data.Data
import GHC.Generics
import Data.Binary

type VarianceInfo = [Variance]

data Variance = Invariant | Bivariant | Contravariant | Covariant
              deriving (Data, Typeable, Show, Generic)

instance Binary Variance
instance NFData Variance
