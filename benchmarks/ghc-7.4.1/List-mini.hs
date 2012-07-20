{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
   foldr1
 ) where

import Data.Maybe
import GHC.Base

--{-@ assert length :: forall a. xs:[a] -> {v: Int | v = len(xs)}  @-}
--length                  :: [a] -> Int
--length l                =  len l 0#
--  where
--    len :: [a] -> Int# -> Int
--    len []     a# = I# a#
--    len (_:xs) a# = len xs (a# +# 1#)
--
--go :: [a] -> Int# -> Int
--go []     a# = I# a#
--go (_:xs) a# = go xs (a# +# 1#) 

{-@ assert errorEmptyList :: {v: String | (0 = 1)} -> a @-}
errorEmptyList :: String -> a
errorEmptyList fun =
  error (prel_list_str ++ fun ++ ": empty list")

prel_list_str :: String
prel_list_str = "Prelude."

{-@ assert foldr1       :: forall a. (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a @-}
foldr1                  :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]            =  x
foldr1 f (x:xs)         =  f x (foldr1 f xs)
foldr1 _ []             =  errorEmptyList "foldr1"


