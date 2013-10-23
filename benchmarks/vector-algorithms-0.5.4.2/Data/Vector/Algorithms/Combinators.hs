{-# LANGUAGE Rank2Types, TypeOperators #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Combinators
-- Copyright   : (c) 2008-2010 Dan Doel
-- Maintainer  : Dan Doel <dan.doel@gmail.com>
-- Stability   : Experimental
-- Portability : Non-portable (rank-2 types)
--
-- The purpose of this module is to supply various combinators for commonly
-- used idioms for the algorithms in this package. Examples at the time of
-- this writing include running an algorithm keyed on some function of the
-- elements (but only computing said function once per element), and safely
-- applying the algorithms on mutable arrays to immutable arrays.

module Data.Vector.Algorithms.Combinators
       (
--       , usingKeys
--       , usingIxKeys
       ) where

import Prelude hiding (length)

import Control.Monad.ST

import Data.Ord

import Data.Vector.Generic

import qualified Data.Vector.Generic.Mutable as M
import qualified Data.Vector.Generic.New     as N

{-
-- | Uses a function to compute a key for each element which the
-- algorithm should use in lieu of the actual element. For instance:
--
-- > usingKeys sortBy f arr
--
-- should produce the same results as:
--
-- > sortBy (comparing f) arr
--
-- the difference being that usingKeys computes each key only once
-- which can be more efficient for expensive key functions.
usingKeys :: (UA e, UA k, Ord k)
          => (forall e'. (UA e') => Comparison e' -> MUArr e' s -> ST s ())
          -> (e -> k)
          -> MUArr e s
          -> ST s ()
usingKeys algo f arr = usingIxKeys algo (const f) arr
{-# INLINE usingKeys #-}

-- | As usingKeys, only the key function has access to the array index
-- at which each element is stored.
usingIxKeys :: (UA e, UA k, Ord k)
            => (forall e'. (UA e') => Comparison e' -> MUArr e' s -> ST s ())
            -> (Int -> e -> k)
            -> MUArr e s
            -> ST s ()
usingIxKeys algo f arr = do
  keys <- newMU (lengthMU arr)
  fill len keys
  algo (comparing fstS) (unsafeZipMU keys arr)
 where
 len = lengthMU arr
 fill k keys
   | k < 0     = return ()
   | otherwise = readMU arr k >>= writeMU keys k . f k >> fill (k-1) keys
{-# INLINE usingIxKeys #-}
-}
