module GhcSort where

import Language.Haskell.Liquid.Prelude
-- This is SAFE
{-@ mymax :: forall <p :: a -> Bool>. (Ord a) => a<p> -> a<p> -> a<p> @-}
mymax a b
  | a > b     = a
  | otherwise = b

foo = mymax n m
  where n = choose 0
        m = choose 0


