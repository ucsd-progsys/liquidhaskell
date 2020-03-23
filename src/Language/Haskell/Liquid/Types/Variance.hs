{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Language.Haskell.Liquid.Types.Variance ( Variance(..), VarianceInfo ) where

import Prelude hiding (error)
import Control.DeepSeq
import Data.Typeable
import Data.Data
import GHC.Generics
import Data.Binary
import Data.Hashable
import Text.PrettyPrint.HughesPJ
import qualified Language.Fixpoint.Types as F

import Language.Haskell.Liquid.Types.Generics

type VarianceInfo = [Variance]

data Variance = Invariant | Bivariant | Contravariant | Covariant
              deriving (Eq, Data, Typeable, Show, Generic)
              deriving Hashable via Generically Variance

instance Binary Variance
instance NFData Variance
instance F.PPrint Variance where
  pprintTidy _ = text . show
