{-# LANGUAGE BangPatterns, Rank2Types, UnboxedTuples #-}

-- |
-- Module      : Data.Text.Private
-- Copyright   : (c) 2011 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com
-- Stability   : experimental
-- Portability : GHC

module Data.Text.Private
    (
      runText
    , span_
    ) where

import Control.Monad.ST (ST, runST)
import Data.Text.Internal (Text(..), textP)
import Data.Text.Unsafe (Iter(..), iter)
import qualified Data.Text.Array as A

span_ :: (Char -> Bool) -> Text -> (# Text, Text #)
span_ p t@(Text arr off len) = (# hd,tl #)
  where hd = textP arr off k
        tl = textP arr (off+k) (len-k)
        !k = loop 0
        loop !i | i < len && p c = loop (i+d)
                | otherwise      = i
            where Iter c d       = iter t i
{-# INLINE span_ #-}

runText :: (forall s. (A.MArray s -> Int -> ST s Text) -> ST s Text) -> Text
runText act = runST (act $ \ !marr !len -> do
                             arr <- A.unsafeFreeze marr
                             return $! textP arr 0 len)
{-# INLINE runText #-}
