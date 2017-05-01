{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Vector
-- Copyright   :  (c) Alberto Ruiz 2007-10
-- License     :  GPL
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
--
-- 1D arrays suitable for numeric computations using external libraries.
--
-- This module provides basic functions for manipulation of structure.
--
-----------------------------------------------------------------------------

module Data.Packed.Vector (
    Vector,
    fromList, (|>), toList, buildVector,
    dim, (@>),
    subVector, takesV, join,
    mapVector, mapVectorWithIndex, zipVector, zipVectorWith, unzipVector, unzipVectorWith,
    mapVectorM, mapVectorM_, mapVectorWithIndexM, mapVectorWithIndexM_,
    foldLoop, foldVector, foldVectorG, foldVectorWithIndex
) where

import Data.Packed.Internal.Vector
import Foreign.Storable

-------------------------------------------------------------------

#ifdef BINARY

import Data.Binary
import Control.Monad(replicateM)

-- a 64K cache, with a Double taking 13 bytes in Bytestring,
-- implies a chunk size of 5041
chunk :: Int
chunk = 5000

chunks :: Int -> [Int]
chunks d = let c = d `div` chunk
               m = d `mod` chunk
           in if m /= 0 then reverse (m:(replicate c chunk)) else (replicate c chunk)  

putVector v = do
              let d = dim v
              mapM_ (\i -> put $ v @> i) [0..(d-1)]

getVector d = do
              xs <- replicateM d get
              return $! fromList xs

instance (Binary a, Storable a) => Binary (Vector a) where
    put v = do
            let d = dim v
            put d
            mapM_ putVector $! takesV (chunks d) v
    get = do
          d <- get
          vs <- mapM getVector $ chunks d
          return $! join vs

#endif

-------------------------------------------------------------------

{- | creates a Vector of the specified length using the supplied function to
     to map the index to the value at that index.

@> buildVector 4 fromIntegral
4 |> [0.0,1.0,2.0,3.0]@

-}
buildVector :: Storable a => Int -> (Int -> a) -> Vector a
buildVector len f =
    fromList $ map f [0 .. (len - 1)]


-- | zip for Vectors
zipVector :: (Storable a, Storable b, Storable (a,b)) => Vector a -> Vector b -> Vector (a,b)
zipVector = zipVectorWith (,)

-- | unzip for Vectors
unzipVector :: (Storable a, Storable b, Storable (a,b)) => Vector (a,b) -> (Vector a,Vector b)
unzipVector = unzipVectorWith id

-------------------------------------------------------------------
