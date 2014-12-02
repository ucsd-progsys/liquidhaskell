{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.Variance (
    Variance(..), VarianceInfo
	) where

import Data.Typeable
import Data.Data

type VarianceInfo = [Variance]
data Variance = Invariant | Bivariant | Contravariant | Covariant deriving (Data, Typeable, Show)