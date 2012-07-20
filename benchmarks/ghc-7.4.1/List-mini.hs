{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
   length
 ) where

import Data.Maybe
import GHC.Base

{-@ assert length :: forall a. xs:[a] -> {v: Int | v = len(xs)}  @-}
length                  :: [a] -> Int
length l                =  len l 0#
  where
    len :: [a] -> Int# -> Int
    len []     a# = I# a#
    len (_:xs) a# = len xs (a# +# 1#)

go :: [a] -> Int# -> Int
go []     a# = I# a#
go (_:xs) a# = go xs (a# +# 1#) 

{-@ assert scanl        :: forall a, b. (a -> b -> a) -> a -> xs:[b] -> {v: [a] | len(v) = 1 + len(xs) } @-}
scanl                   :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q ls            =  q : (case ls of
                                []   -> []
                                x:xs -> scanl f (f q x) xs)


