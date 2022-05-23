{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.Conversion
-- Copyright   :  (c) Alberto Ruiz 2010
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable
--
-- Conversion routines
--
-----------------------------------------------------------------------------

module Numeric.Conversion (
    Complexable(..), RealElement,
    module Data.Complex
) where

import Data.Packed.Internal.Vector
import Data.Packed.Internal.Matrix
import Data.Complex
import Control.Arrow((***))

-------------------------------------------------------------------

-- | Supported single-double precision type pairs
class (Element s, Element d) => Precision s d | s -> d, d -> s where
    double2FloatG :: Vector d -> Vector s
    float2DoubleG :: Vector s -> Vector d

instance Precision Float Double where
    double2FloatG = double2FloatV
    float2DoubleG = float2DoubleV

instance Precision (Complex Float) (Complex Double) where
    double2FloatG = asComplex . double2FloatV . asReal
    float2DoubleG = asComplex . float2DoubleV . asReal

-- | Supported real types
class (Element t, Element (Complex t), RealFloat t
--       , RealOf t ~ t, RealOf (Complex t) ~ t
       )
    => RealElement t

instance RealElement Double
instance RealElement Float


-- | Structures that may contain complex numbers
class Complexable c where
    toComplex'   :: (RealElement e) => (c e, c e) -> c (Complex e)
    fromComplex' :: (RealElement e) => c (Complex e) -> (c e, c e)
    comp'        :: (RealElement e) => c e -> c (Complex e)
    single'      :: Precision a b => c b -> c a
    double'      :: Precision a b => c a -> c b


instance Complexable Vector where
    toComplex' = toComplexV
    fromComplex' = fromComplexV
    comp' v = toComplex' (v,constantD 0 (dim v))
    single' = double2FloatG
    double' = float2DoubleG


-- | creates a complex vector from vectors with real and imaginary parts
toComplexV :: (RealElement a) => (Vector a, Vector a) ->  Vector (Complex a)
toComplexV (r,i) = asComplex $ flatten $ fromColumns [r,i]

-- | the inverse of 'toComplex'
fromComplexV :: (RealElement a) => Vector (Complex a) -> (Vector a, Vector a)
fromComplexV z = (r,i) where
    [r,i] = toColumns $ reshape 2 $ asReal z


instance Complexable Matrix where
    toComplex' = uncurry $ liftMatrix2 $ curry toComplex'
    fromComplex' z = (reshape c *** reshape c) . fromComplex' . flatten $ z
        where c = cols z
    comp' = liftMatrix comp'
    single' = liftMatrix single'
    double' = liftMatrix double'

