{-# LANGUAGE BangPatterns, Rank2Types, UnboxedTuples #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

--LIQUID FIXME: the original type used unboxed tuples, (# Text, Text #)
{-@ span_ :: (Char -> Bool) -> t:Text -> ( TextLE t, TextLE t ) @-}
span_ :: (Char -> Bool) -> Text -> ( Text, Text )
span_ p t@(Text arr off len) = ( hd,tl )
  where hd = textP arr off k
        tl = textP arr (off+k) (len-k)
        !k = loop len 0
--LIQUID         loop !i | i < len && p c = loop (i+d)
--LIQUID                 | otherwise      = i
--LIQUID             where Iter c d       = iter t i
        loop (d :: Int) !i | i < len = let Iter c d' = iter t i
                                       in if p c then loop (d-d') (i+d') else i
                           | otherwise = i
{-# INLINE span_ #-}

{-@ runText :: (forall s. (m:A.MArray s -> MAValidO m -> ST s Text) -> ST s Text)
            -> Text
  @-}
runText :: (forall s. (A.MArray s -> Int -> ST s Text) -> ST s Text) -> Text
runText act = runST (act $ \ !marr !len -> do
                             arr <- A.unsafeFreeze marr
                             return $! textP arr 0 len)
{-# INLINE runText #-}
