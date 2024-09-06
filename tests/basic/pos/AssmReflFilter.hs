-- | Real-case example for `assume reflect` using the Prelude
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"    	@-}

module AssmReflFilter where

import Data.List (filter)
import Data.Char (isDigit)

-- Reflect filter
{-@ reflect myfilter @-}
{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a] | len xs >= len v} @-}
myfilter :: (a -> Bool) -> [a] -> [a]
myfilter _pred []	= []
myfilter pred (x:xs)
  | pred x     	= x : myfilter pred xs
  | otherwise  	= myfilter pred xs

{-@ assume reflect filter as myfilter @-}

-- Reflect (<=)

{-@ reflect myLt @-}
myLt :: Ord a => a -> a -> Bool 
myLt x y = x <= y

{-@ assume reflect (<=) as myLt @-}

-- My function to reflect

{-@ reflect onlyBiggerThan @-}
onlyBiggerThan :: Int -> [Int] -> [Int]
onlyBiggerThan x = filter ((<=) x)

{-@ g :: xs:[Int] -> {v:[Int] | len xs >= len v} @-}
g :: [Int] -> [Int]
g xs = filter ((<=) 5) xs

-- Another one
{-@ reflect myIsDigit @-}
myIsDigit :: Char -> Bool
myIsDigit x = '0' <= x && x <= '9'

{-@ assume reflect isDigit as myIsDigit @-}

{-@ reflect keepDigits @-}
keepDigits :: [Char] -> [Char]
keepDigits = filter isDigit

{-@ lemma :: {v:[Char] | v == []} @-}
lemma::  [Char]
lemma = filter isDigit []