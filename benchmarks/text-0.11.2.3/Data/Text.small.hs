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
import qualified Data.Text.Array as A
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
import qualified Data.Text.Array
import qualified Data.Text.Unsafe
import qualified Data.Word
import Language.Haskell.Liquid.Prelude

{-@ init :: t:{v:Data.Text.Internal.Text | (tlength v) > 0}
         -> {v:Data.Text.Internal.Text | ((tlength v) = ((tlength t) - 1))}
  @-}
init :: Text -> Text
init t@(Text arr off len)
    | len <= 0                   = liquidError "init"
    | n >= 0xDC00 && n <= 0xDFFF = textP arr off (len-2)
    | otherwise                  = textP arr off (len-1)
    where
      --LIQUID n = A.unsafeIndex arr (off+len-1)
      n = A.unsafeIndexB arr off len (off+len-1)
{-# INLINE [1] init #-}
