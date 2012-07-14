{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
   mylength
 ) where

import Data.Maybe
import GHC.Base

{-@ assert mylength :: forall a. xs:[a] -> {v: Int | v + 1 = len(xs)}  @-}
mylength                  :: [a] -> Int
-- mylength l                =  go l 0# 
mylength l                =  lenJHALA l 0#
  where
    lenJHALA :: [a] -> Int# -> Int
    lenJHALA []     a# = I# a#
    lenJHALA (_:xs) a# = lenJHALA xs (a# +# 1#)

go :: [a] -> Int# -> Int
go []     a# = I# a#
go (_:xs) a# = go xs (a# +# 1#) 
