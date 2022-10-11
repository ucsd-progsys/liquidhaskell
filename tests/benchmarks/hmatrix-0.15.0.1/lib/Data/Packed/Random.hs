-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Vector
-- Copyright   :  (c) Alberto Ruiz 2009
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
--
-- Random vectors and matrices.
--
-----------------------------------------------------------------------------

module Data.Packed.Random (
    Seed,
    RandDist(..),
    randomVector,
    gaussianSample,
    uniformSample
) where

import Numeric.GSL.Vector
import Data.Packed
import Numeric.ContainerBoot
import Numeric.LinearAlgebra.Algorithms


type Seed = Int

-- | Obtains a matrix whose rows are pseudorandom samples from a multivariate
-- Gaussian distribution.
gaussianSample :: Seed
               -> Int -- ^ number of rows
               -> Vector Double -- ^ mean vector
               -> Matrix Double -- ^ covariance matrix
               -> Matrix Double -- ^ result
gaussianSample seed n med cov = m where
    c = dim med
    meds = konst 1 n `outer` med
    rs = reshape c $ randomVector seed Gaussian (c * n)
    m = rs `mXm` cholSH cov `add` meds

-- | Obtains a matrix whose rows are pseudorandom samples from a multivariate
-- uniform distribution.
uniformSample :: Seed
               -> Int -- ^ number of rows
               -> [(Double,Double)] -- ^ ranges for each column
               -> Matrix Double -- ^ result
uniformSample seed n rgs = m where
    (as,bs) = unzip rgs
    a = fromList as
    cs = zipWith subtract as bs
    d = dim a
    dat = toRows $ reshape n $ randomVector seed Uniform (n*d)
    am = konst 1 n `outer` a
    m = fromColumns (zipWith scale cs dat) `add` am

