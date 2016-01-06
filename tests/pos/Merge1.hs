module Merge1 where

{-@ merge1 :: Ord a
           => xs:[a]
           -> ys:[a]
           -> {v:[a] | len v == len xs + len ys}
           / [len xs + len ys]
  @-}
merge1 :: Ord a => [a] -> [a] -> [a]
merge1 (a:as') (b:bs')
  | a `compare` b == GT = b:merge1 (a:as')  bs'
  | otherwise           = a:merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as
