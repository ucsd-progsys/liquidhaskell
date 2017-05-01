{-# LANGUAGE CPP #-}
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntMap
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of maps from integer keys to values
-- (dictionaries).
--
-- This module re-exports the value lazy 'Data.IntMap.Lazy' API, plus
-- several value strict functions from 'Data.IntMap.Strict'.
--
-- These modules are intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import Data.IntMap (IntMap)
-- >  import qualified Data.IntMap as IntMap
--
-- The implementation is based on /big-endian patricia trees/.  This data
-- structure performs especially well on binary operations like 'union'
-- and 'intersection'.  However, my benchmarks show that it is also
-- (much) faster on insertions and deletions when compared to a generic
-- size-balanced map implementation (see "Data.Map").
--
--    * Chris Okasaki and Andy Gill,  \"/Fast Mergeable Integer Maps/\",
--      Workshop on ML, September 1998, pages 77-86,
--      <http://citeseer.ist.psu.edu/okasaki98fast.html>
--
--    * D.R. Morrison, \"/PATRICIA -- Practical Algorithm To Retrieve
--      Information Coded In Alphanumeric/\", Journal of the ACM, 15(4),
--      October 1968, pages 514-534.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation <http://en.wikipedia.org/wiki/Big_O_notation>.
-- Many operations have a worst-case complexity of /O(min(n,W))/.
-- This means that the operation can become linear in the number of
-- elements with a maximum of /W/ -- the number of bits in an 'Int'
-- (32 or 64).
-----------------------------------------------------------------------------

module Data.IntMap
    ( module Data.IntMap.Lazy
    , insertWith'
    , insertWithKey'
    , fold
    , foldWithKey
    ) where

import Prelude hiding (lookup,map,filter,foldr,foldl,null)
import Data.IntMap.Lazy
import qualified Data.IntMap.Strict as S

-- | /Deprecated./ As of version 0.5, replaced by 'S.insertWith'.
--
-- /O(log n)/. Same as 'insertWith', but the combining function is
-- applied strictly.  This function is deprecated, use 'insertWith' in
-- "Data.IntMap.Strict" instead.
insertWith' :: (a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWith' = S.insertWith
{-# INLINE insertWith' #-}

-- | /Deprecated./ As of version 0.5, replaced by 'S.insertWithKey'.
--
-- /O(log n)/. Same as 'insertWithKey', but the combining function is
-- applied strictly.  This function is deprecated, use 'insertWithKey'
-- in "Data.IntMap.Strict" instead.
insertWithKey' :: (Key -> a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWithKey' = S.insertWithKey
{-# INLINE insertWithKey' #-}

-- | /Deprecated./ As of version 0.5, replaced by 'foldr'.
--
-- /O(n)/. Fold the values in the map using the given
-- right-associative binary operator. This function is an equivalent
-- of 'foldr' and is present for compatibility only.
fold :: (a -> b -> b) -> b -> IntMap a -> b
fold = foldr
{-# INLINE fold #-}

-- | /Deprecated./ As of version 0.5, replaced by 'foldrWithKey'.
--
-- /O(n)/. Fold the keys and values in the map using the given
-- right-associative binary operator. This function is an equivalent
-- of 'foldrWithKey' and is present for compatibility only.
foldWithKey :: (Int -> a -> b -> b) -> b -> IntMap a -> b
foldWithKey = foldrWithKey
{-# INLINE foldWithKey #-}
