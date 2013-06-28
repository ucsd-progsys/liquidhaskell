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
import qualified Data.Text
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Fusion.Size
import qualified Data.Text.Internal
import qualified Data.Text.Lazy.Fusion
import qualified Data.Text.Lazy.Internal
import qualified Data.Text.Private
import qualified Data.Text.Search
import qualified Data.Text.Unsafe
import Language.Haskell.Liquid.Prelude

{-@ splitAt :: n:{v:Int64 | v >= 0}
            -> t:Data.Text.Lazy.Internal.Text
            -> ({v:Data.Text.Lazy.Internal.Text | (Min (ltlength v) (ltlength t) n)}
               , Data.Text.Lazy.Internal.Text)<{\spx spy ->
                 (ltlength spy) = ((ltlength t) - (ltlength spx))}>
  @-}
splitAt :: Int64 -> Text -> (Text, Text)
--LIQUID splitAt = loop
--LIQUID   where loop _ Empty      = (empty, empty)
--LIQUID         loop n t | n <= 0 = (empty, t)
--LIQUID         loop n (Chunk t ts)
--LIQUID              | n < len   = let (t',t'') = T.splitAt (fromIntegral n) t
--LIQUID                            in (Chunk t' Empty, Chunk t'' ts)
--LIQUID              | otherwise = let (ts',ts'') = loop (n - len) ts
--LIQUID                            in (Chunk t ts', ts'')
--LIQUID              where len = fromIntegral (T.length t)
splitAt _ Empty      = (empty, empty)
splitAt n t | n <= 0 = (empty, t)
splitAt n (Chunk t ts)
    | n < len   = let (t',t'') = T.splitAt (fromIntegral n) t
                  in (Chunk t' Empty, Chunk t'' ts)
    | otherwise = let (ts',ts'') = splitAt (n - len) ts
                  in (Chunk t ts', ts'')
    where len = fromIntegral (T.length t)
