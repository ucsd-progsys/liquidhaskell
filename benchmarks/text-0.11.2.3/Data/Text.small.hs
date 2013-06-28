{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types, UnboxedTuples #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Data.Text
-- Copyright   : (c) 2009, 2010, 2011, 2012 Bryan O'Sullivan,
--               (c) 2009 Duncan Coutts,
--               (c) 2008, 2009 Tom Harper
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- A time and space-efficient implementation of Unicode text.
-- Suitable for performance critical use, both in terms of large data
-- quantities and high speed.
--
-- /Note/: Read below the synopsis for important notes on the use of
-- this module.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions, e.g.
--
-- > import qualified Data.Text as T
--
-- To use an extended and very rich family of functions for working
-- with Unicode text (including normalization, regular expressions,
-- non-standard encodings, text breaking, and locales), see the
-- @text-icu@ package: <http://hackage.haskell.org/package/text-icu>

module Data.Text where

import Prelude (Char, Bool(..), Int, Maybe(..), String,
                Eq(..), Ord(..), Ordering(..), (++),
                Read(..), Show(..),
                (&&), (||), (+), (-), (.), ($), ($!), (>>), (*),
                div, maxBound, not, return, otherwise)
#if defined(HAVE_DEEPSEQ)
import Control.DeepSeq (NFData)
#endif
#if defined(ASSERTS)
import Control.Exception (assert)
#endif
import Data.Char (isSpace)
import Data.Data (Data(gfoldl, toConstr, gunfold, dataTypeOf))
#if __GLASGOW_HASKELL__ >= 612
import Data.Data (mkNoRepType)
#else
import Data.Data (mkNorepType)
#endif
import Control.Monad (foldM)
import qualified Data.Text.Array as A
import qualified Data.List as L
import Data.Monoid (Monoid(..))
import Data.String (IsString(..))
import qualified Data.Text.Fusion as S
import qualified Data.Text.Fusion.Common as S
import Data.Text.Fusion (stream, reverseStream, unstream)
import Data.Text.Private (span_)
import Data.Text.Internal (Text(..), empty, firstf, safe, text, textP)
import qualified Prelude as P
import Data.Text.Unsafe (Iter(..), iter,
                         iter_, lengthWord16, reverseIter,
                         unsafeHead, unsafeTail)
import Data.Text.UnsafeChar (unsafeChr)
import qualified Data.Text.Util as U
import qualified Data.Text.Encoding.Utf16 as U16
import Data.Text.Search (indices)
#if defined(__HADDOCK__)
import Data.ByteString (ByteString)
import qualified Data.Text.Lazy as L
import Data.Int (Int64)
#endif
--LIQUID #if __GLASGOW_HASKELL__ >= 702
--LIQUID import qualified GHC.CString as GHC
--LIQUID #else
--LIQUID import qualified GHC.Base as GHC
--LIQUID #endif
--LIQUID import GHC.Prim (Addr#)


--LIQUID
import Prelude (Integer(..), Num(..), Real(..), Integral(..))
import Data.Word --(Word16(..))
import Data.Text.Axioms
import qualified Data.Text.Array
import qualified Data.Text.Internal
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Fusion.Size
import qualified Data.Text.Search
import Language.Haskell.Liquid.Prelude
import qualified GHC.ST

{-@ splitAt :: n:{v:Int | v >= 0}
            -> t:Data.Text.Internal.Text
            -> ( {v:Data.Text.Internal.Text | (Min (tlength v) (tlength t) n)}
               , Data.Text.Internal.Text)<{\x y ->
                              ((tlength y) = ((tlength t) - (tlength x)))}>
  @-}
splitAt :: Int -> Text -> (Text, Text)
splitAt n t@(Text arr off len)
    | n <= 0    = (empty, t)
    | n >= len  = (t, empty)
    | otherwise = loop 0 0
--LIQUID    | otherwise = (Text arr off k, Text arr (off+k) (len-k))
--LIQUID  where k = loop_splitAt t n 0 0
--LIQUID        loop !i !cnt
--LIQUID            | i >= len || cnt >= n = i
--LIQUID            | otherwise            = loop (i+d) (cnt+1)
--LIQUID            where d                = iter_ t i
    where loop !i !cnt
              | i >= len || cnt >= n = let len' = liquidAssume (axiom_numchars_split t i) (len-i)
                                       in ( Text arr off i
                                          , Text arr (off+i) len')
              | otherwise            = let d = iter_ t i
                                           cnt' = cnt + 1
                                       in loop (i+d) cnt'
{-# INLINE splitAt #-}

{-@ tails :: t:Data.Text.Internal.Text
          -> [{v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}]<{\x y ->
              (tlength x) > (tlength y)}>
  @-}
tails :: Text -> [Text]
tails t | null t    = [empty]
        | otherwise = t : tails (unsafeTail t)

{-@ null :: t:Data.Text.Internal.Text
         -> {v:Bool | ((Prop v) <=> ((tlength t) = 0))}
  @-}
null :: Text -> Bool
null (Text _arr _off len) =
--LIQUID #if defined(ASSERTS)
    liquidAssert (len >= 0) $
--LIQUID #endif
    len <= 0
{-# INLINE [1] null #-}
