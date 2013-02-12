-- |
-- Module      : Data.Text.Encoding.Utf32
-- Copyright   : (c) 2008, 2009 Tom Harper,
--               (c) 2009, 2010 Bryan O'Sullivan,
--               (c) 2009 Duncan Coutts
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- Basic UTF-32 validation.
module Data.Text.Encoding.Utf32
    (
      validate
    ) where

import Data.Word (Word32)

validate    :: Word32 -> Bool
validate x1 = x1 < 0xD800 || (x1 > 0xDFFF && x1 <= 0x10FFFF)
{-# INLINE validate #-}
