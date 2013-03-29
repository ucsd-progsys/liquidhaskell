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
-- #if defined(HAVE_DEEPSEQ)
-- import Control.DeepSeq (NFData)
-- #endif
-- #if defined(ASSERTS)
-- import Control.Exception (assert)
-- #endif
-- import Data.Char (isSpace)
-- import Data.Data (Data(gfoldl, toConstr, gunfold, dataTypeOf))
-- #if __GLASGOW_HASKELL__ >= 612
-- import Data.Data (mkNoRepType)
-- #else
-- import Data.Data (mkNorepType)
-- #endif
-- import Control.Monad (foldM)
import qualified Data.Text.Array as A (Array)
-- import qualified Data.List as L
-- import Data.Monoid (Monoid(..))
-- import Data.String (IsString(..))
-- import qualified Data.Text.Fusion as S
-- import qualified Data.Text.Fusion.Common as S
-- import Data.Text.Fusion (stream, reverseStream, unstream)
-- import Data.Text.Private (span_)
import Data.Text.Internal (Text(..), empty, firstf, safe, text, textP)
import qualified Prelude as P
import Data.Text.Unsafe (iter_)
-- import Data.Text.UnsafeChar (unsafeChr)
-- import qualified Data.Text.Util as U
-- import qualified Data.Text.Encoding.Utf16 as U16
-- import Data.Text.Search (indices)
-- #if defined(__HADDOCK__)
-- import Data.ByteString (ByteString)
-- import qualified Data.Text.Lazy as L
-- import Data.Int (Int64)
-- #endif
-- #if __GLASGOW_HASKELL__ >= 702
-- import qualified GHC.CString as GHC
-- #else
-- import qualified GHC.Base as GHC
-- #endif
-- import GHC.Prim (Addr#)


--LIQUID
import Prelude (Integer(..), Num(..), Real(..), Integral(..))
--import Data.Word --(Word16(..))
--import Data.Text.Axioms
import Language.Haskell.Liquid.Prelude

{-@ drop :: n:{v:Int | v >= 0}
         -> t:Text
         -> {v:Text | ((tlength v) = ((((tlength t) - n) <= 0) ? 0 : ((tlength t) - n)))}
  @-}
         -- -> {v:Text | ((((tlen t) > n)  <=> ((tlen v) = ((tlen t) - n)))
         --            && (((tlen t) <= n) <=> ((tlen v) = 0)))}
--LIQUID          -> {v:Text | (tlen v) <= ((tlen t) - n)}
drop :: Int -> Text -> Text
drop = drop'
drop' n t@(Text arr off len)
    | n <= 0    = t
    | n >= len  = empty
    | otherwise = loop_drop n t 0 0
  -- where loop !i !cnt
  --           | i >= len || cnt >= n   = P.id $ Text arr (off+i) (P.id (len-i))
  --           | i <  len && cnt <  n   = let d = iter_ t i
  --                                      in loop (i+d) (cnt+1)
--LIQUID            where d = iter_ t i
{-@ loop_drop :: n:{v:Int | v >= 0}
              -> t:Text
              -> i:{v:Int | ((v >= 0) && (v <= (tlen t)))}
              -> cnt:{v:Int | (((numchars (tarr t) (toff t) i) = v)
                            && (v <= n))}
              -> {v:Text | ((tlength v) = ((((tlength t) - n) <= 0) ? 0 : ((tlength t) - n)))}
  @-}
loop_drop :: Int -> Text -> Int -> Int -> Text
loop_drop n t@(Text arr off len) !i !cnt
    | i >= len               = liquidAssert (nc arr off (len-i) <= n)
                               $ Text arr (off+i) (P.id (len-i))
    | cnt == n               = liquidAssert ((tl t) >= 0)
                               $ Text arr (off+i) (P.id (len-i))
    | i <  len && cnt <  n   = let d = iter_ t i
                               in loop_drop n t (i+d) (cnt+1)

{-@ nc :: a:A.Array -> o:Int -> l:Int -> {v:Int | v = (numchars a o l)} @-}
nc :: A.Array -> Int -> Int -> Int
nc = P.undefined

{-@ tl :: t:Text -> {v:Int | v = (tlength t)} @-}
tl :: Text -> Int
tl = P.undefined

-- emptyError :: String -> a
-- emptyError fun = liquidError $ "Data.Text." ++ fun ++ ": empty input"

-- overflowError :: String -> a
-- overflowError fun = P.error $ "Data.Text." ++ fun ++ ": size overflow"
