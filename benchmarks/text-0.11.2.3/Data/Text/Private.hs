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

--LIQUID
import qualified Data.Text.Array


span_ :: (Char -> Bool) -> Text -> (# Text, Text #)
span_ p t@(Text arr off len) = (# hd,tl #)
  where hd = textP arr off k
        tl = textP arr (off+k) (len-k)
        !k = loop 0
--LIQUID         loop !i | i < len && p c = loop (i+d)
--LIQUID                 | otherwise      = i
--LIQUID             where Iter c d       = iter t i
        loop !i | i < len = let Iter c d = iter t i
                            in if p c then loop (i+d) else i
                | otherwise = i
{-# INLINE span_ #-}

{-@ runText :: (forall s. (ma:Data.Text.Array.MArray s
                           -> {v:Nat | v <= (malen ma)}
                           -> GHC.ST.ST s Text)
                       -> GHC.ST.ST s Text)
            -> Data.Text.Internal.Text
  @-}
runText :: (forall s. (A.MArray s -> Int -> ST s Text) -> ST s Text) -> Text
runText act = runST (act $ \ !marr !len -> do
                             arr <- A.unsafeFreeze marr
                             return $! textP arr 0 len)
{-# INLINE runText #-}
