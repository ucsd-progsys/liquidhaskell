{-# LANGUAGE CPP #-}
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Safe #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Map
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of ordered maps from keys to values
-- (dictionaries).
--
-- This module re-exports the value lazy 'Data.Map.Lazy' API, plus
-- several value strict functions from 'Data.Map.Strict'.
--
-- These modules are intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import qualified Data.Map as Map
--
-- The implementation of 'Map' is based on /size balanced/ binary trees (or
-- trees of /bounded balance/) as described by:
--
--    * Stephen Adams, \"/Efficient sets: a balancing act/\",
--     Journal of Functional Programming 3(4):553-562, October 1993,
--     <http://www.swiss.ai.mit.edu/~adams/BB/>.
--
--    * J. Nievergelt and E.M. Reingold,
--      \"/Binary search trees of bounded balance/\",
--      SIAM journal of computing 2(1), March 1973.
--
-- Note that the implementation is /left-biased/ -- the elements of a
-- first argument are always preferred to the second, for example in
-- 'union' or 'insert'.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation (<http://en.wikipedia.org/wiki/Big_O_notation>).
-----------------------------------------------------------------------------

module Data.Map
    ( module Data.Map.Lazy
    , insertWith'
    , insertWithKey'
    , insertLookupWithKey'
    , fold
    , foldWithKey
    ) where

import Data.Map.Lazy
import qualified Data.Map.Lazy as L
import qualified Data.Map.Strict as S

-- | /Deprecated./ As of version 0.5, replaced by 'S.insertWith'.
--
-- /O(log n)/. Same as 'insertWith', but the combining function is
-- applied strictly.  This is often the most desirable behavior.
--
-- For example, to update a counter:
--
-- > insertWith' (+) k 1 m
--
insertWith' :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith' = S.insertWith
{-# INLINABLE insertWith' #-}

-- | /Deprecated./ As of version 0.5, replaced by 'S.insertWithKey'.
--
-- /O(log n)/. Same as 'insertWithKey', but the combining function is
-- applied strictly.
insertWithKey' :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithKey' = S.insertWithKey
{-# INLINABLE insertWithKey' #-}

-- | /Deprecated./ As of version 0.5, replaced by
-- 'S.insertLookupWithKey'.
--
-- /O(log n)/. A strict version of 'insertLookupWithKey'.
insertLookupWithKey' :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a
                     -> (Maybe a, Map k a)
insertLookupWithKey' = S.insertLookupWithKey
{-# INLINABLE insertLookupWithKey' #-}

-- | /Deprecated./ As of version 0.5, replaced by 'L.foldr'.
--
-- /O(n)/. Fold the values in the map using the given right-associative
-- binary operator. This function is an equivalent of 'foldr' and is present
-- for compatibility only.
fold :: (a -> b -> b) -> b -> Map k a -> b
fold = L.foldr
{-# INLINE fold #-}

-- | /Deprecated./ As of version 0.4, replaced by 'L.foldrWithKey'.
--
-- /O(n)/. Fold the keys and values in the map using the given right-associative
-- binary operator. This function is an equivalent of 'foldrWithKey' and is present
-- for compatibility only.
foldWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
foldWithKey = foldrWithKey
{-# INLINE foldWithKey #-}
