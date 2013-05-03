{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns, MagicHash, CPP #-}
-- |
-- Module      : Data.Text.Lazy
-- Copyright   : (c) 2009, 2010, 2012 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- A time and space-efficient implementation of Unicode text using
-- lists of packed arrays.
--
-- /Note/: Read below the synopsis for important notes on the use of
-- this module.
--
-- The representation used by this module is suitable for high
-- performance use and for streaming large quantities of data.  It
-- provides a means to manipulate a large body of text without
-- requiring that the entire content be resident in memory.
--
-- Some operations, such as 'concat', 'append', 'reverse' and 'cons',
-- have better time complexity than their "Data.Text" equivalents, due
-- to the underlying representation being a list of chunks. For other
-- operations, lazy 'Text's are usually within a few percent of strict
-- ones, but often with better heap usage if used in a streaming
-- fashion. For data larger than available memory, or if you have
-- tight memory constraints, this module will be the only option.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions.  eg.
--
-- > import qualified Data.Text.Lazy as L

module Data.Text.Lazy  where

import Prelude (Char, Bool(..), Maybe(..), String,
                Eq(..), Ord(..), Ordering(..), Read(..), Show(..),
                (&&), (||), (+), (-), (.), ($), (++),
                div, error, flip, fmap, fromIntegral, not, otherwise
               -- LIQUID
               , Num(..), Integral(..), Integer)
import qualified Prelude as P
#if defined(HAVE_DEEPSEQ)
import Control.DeepSeq (NFData(..))
#endif
import Data.Int (Int64)
import qualified Data.List as L
import Data.Char (isSpace)
import Data.Data (Data(gfoldl, toConstr, gunfold, dataTypeOf))
#if __GLASGOW_HASKELL__ >= 612
import Data.Data (mkNoRepType)
#else
import Data.Data (mkNorepType)
#endif
import Data.Monoid (Monoid(..))
import Data.String (IsString(..))
import qualified Data.Text as T
import qualified Data.Text.Internal as T
import qualified Data.Text.Fusion.Common as S
import qualified Data.Text.Unsafe as T
import qualified Data.Text.Lazy.Fusion as S
import Data.Text.Fusion.Internal (PairS(..))
import Data.Text.Lazy.Fusion (stream, unstream)
import Data.Text.Lazy.Internal (Text(..), chunk, empty, foldlChunks, foldrChunks)
import Data.Text.Internal (firstf, safe, textP)
import qualified Data.Text.Util as U
import Data.Text.Lazy.Search (indices)
#if __GLASGOW_HASKELL__ >= 702
import qualified GHC.CString as GHC
#else
import qualified GHC.Base as GHC
#endif
import GHC.Prim (Addr#)

--LIQUID
import Data.Int
import qualified Data.Word
--import qualified Data.Text
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Internal
import qualified Data.Text.Lazy.Internal
import qualified Data.Text.Unsafe
import qualified GHC.Real
import Language.Haskell.Liquid.Prelude

{-@ null :: t:Data.Text.Lazy.Internal.Text
         -> {v:Bool | ((Prop v) <=> ((ltlength t) = 0))}
  @-}
null :: Text -> Bool
null Empty = True
null _     = False
{-# INLINE [1] null #-}

{-@ isSingleton :: t:Data.Text.Lazy.Internal.Text
                -> {v:Bool | ((Prop v) <=> ((ltlength t) = 1))}
  @-}
isSingleton :: Text -> Bool
--LIQUID isSingleton = S.isSingleton . stream
isSingleton t = P.undefined
{-# INLINE isSingleton #-}

{-@ singleton :: Char -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = 1} @-}
singleton :: Char -> Text
singleton c = Chunk (T.singleton c) Empty
{-# INLINE [1] singleton #-}

-- | /O(1)/ Returns the first character of a 'Text', which must be
-- non-empty.  Subject to fusion.
{-@ head :: {v:Data.Text.Lazy.Internal.Text | (ltlength v) > 0}
         -> Char
  @-}
head :: Text -> Char
head t = P.undefined
{-# INLINE head #-}

-- | /O(n)/ Concatenate a list of 'Text's.
{-@ concat :: ts:[Data.Text.Lazy.Internal.Text]
           -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = (sum_ltlengths ts)}
  @-}
concat :: [Text] -> Text
concat = concat_to
  where
    go Empty        css = to css
    go (Chunk c cs) css = Chunk c (go cs css)
    to []               = Empty
    to (cs:css)         = go cs css
--LIQUID concat = to
--LIQUID   where
--LIQUID     go Empty        css = to css
--LIQUID     go (Chunk c cs) css = Chunk c (go cs css)
--LIQUID     to []               = Empty
--LIQUID     to (cs:css)         = go cs css

{-@ concat_go :: t:Data.Text.Lazy.Internal.Text
              -> ts:[Data.Text.Lazy.Internal.Text]
              -> {v:Data.Text.Lazy.Internal.Text | ((ltlength v) = ((sum_ltlengths ts) + (ltlength t)))}
  @-}
concat_go Empty        css = concat_to css
concat_go (Chunk c cs) css = Chunk c (concat_go cs css)

{-@ concat_to :: ts:[Data.Text.Lazy.Internal.Text]
              -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = (sum_ltlengths ts)}
  @-}
concat_to []               = Empty
concat_to (cs:css)         = concat_go cs css
{-# INLINE concat #-}


-- | /O(n*m)/ 'replicate' @n@ @t@ is a 'Text' consisting of the input
-- @t@ repeated @n@ times.
{-@ replicate :: n:{v:Int64 | v >= 0}
              -> t:Data.Text.Lazy.Internal.Text
              -> {v:Data.Text.Lazy.Internal.Text |
                     ((n = 0) ? ((ltlength v) = 0)
                              : ((ltlength v) >= (ltlength t)))}
  @-}
replicate :: Int64 -> Text -> Text
replicate n t
    | null t || n <= 0 = empty
    | isSingleton t    = replicateChar n (head t)
    | otherwise        = let t' = concat (replicate_rep n t 0)
                         in liquidAssert (length t' >= length t) t'

--LIQUID     | otherwise        = concat (rep 0)
--LIQUID     where rep !i | i >= n    = []
--LIQUID                  | otherwise = t : rep (i+1)
{-@ replicate_rep :: n:{v:Int64 | v > 0}
                  -> t:Data.Text.Lazy.Internal.Text
                  -> i:{v:Int64 | ((v >= 0) && (v <= n))}
                  -> {v:[{v0:Data.Text.Lazy.Internal.Text | (ltlength v0) = (ltlength t)}] |
                        ((len v) = (n - i) && (((len v) > 0) <=> ((sum_ltlengths v) >= (ltlength t))))}
  @-}
replicate_rep :: Int64 -> Text -> Int64 -> [Text]
replicate_rep n t !i | i >= n    = []
                     | otherwise = let ts = replicate_rep n t (i+1)
                                       t' = t:ts
                                   in liquidAssert (stl t' >= length t) t'

{-@ stl :: ts:[Data.Text.Lazy.Internal.Text] -> {v:Int64 | v = (sum_ltlengths ts)} @-}
stl :: [Text] -> Int64
stl ts =  1
{-# INLINE replicate #-}

-- | /O(n)/ 'replicateChar' @n@ @c@ is a 'Text' of length @n@ with @c@ the
-- value of every element. Subject to fusion.
{-@ replicateChar :: n:Int64
                  -> Char
                  -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = n}
  @-}
replicateChar :: Int64 -> Char -> Text
--LIQUID replicateChar n c = unstream (S.replicateCharI n (safe c))
replicateChar n c = unstream (S.replicateCharI (fromIntegral n) (safe c))
{-# INLINE replicateChar #-}

{-# RULES
"LAZY TEXT replicate/singleton -> replicateChar" [~1] forall n c.
    replicate n (singleton c) = replicateChar n c
  #-}


{-@ length :: t:Data.Text.Lazy.Internal.Text
           -> {v:Int64 | v = (ltlength t)}
  @-}
length :: Text -> Int64
length t = 1 --P.id $ foldlChunks t go 0 t
  where go l t = l + fromIntegral (T.length t)
-- length = foldlChunks go 0
--     where go l t = l + fromIntegral (T.length t)

-- | /O(c)/ Convert a list of strict 'T.Text's into a lazy 'Text'.
{- fromChunks :: ts:[Data.Text.Internal.Text]
               -> {v:Data.Text.Lazy.Internal.Text | (ltlength v) = (sum_tlengths ts)}
  @-}
-- fromChunks :: [T.Text] -> Text
-- fromChunks cs = L.foldr chunk Empty cs

-- | /O(n)/ Convert a lazy 'Text' into a list of strict 'T.Text's.
{- toChunks :: t:Data.Text.Lazy.Internal.Text
             -> {v:[Data.Text.Internal.Text] | (sum_tlengths v) = (ltlength t)}
  @-}
-- toChunks :: Text -> [T.Text]
-- toChunks cs = foldrChunks (\ts' t ts -> t:ts) [] cs
