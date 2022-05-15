{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple"            @-}

module FilterPLE where

import Prelude hiding (filter)

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect isPos @-} 
isPos :: Int -> Bool
isPos n = n > 0

{-@ reflect isNeg @-} 
isNeg :: Int -> Bool
isNeg n = n < 0

{-@ positives :: [Int] -> [{v:Int | v > 0}] @-}
positives :: [Int] -> [Int]
positives xs = filter isPos xs

{-@ negatives :: [Int] -> [{v:Int | v < 0}] @-}
negatives :: [Int] -> [Int]
negatives xs = filter isNeg xs
