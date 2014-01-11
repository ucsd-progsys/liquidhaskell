module Infinity () where

import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--totality" @-}
{-@ Lazy inf @-}

{-@ inf :: {v:[Int] | (((len v) > oo) && ((len v) > 2))} @-}
inf :: [Int]
inf = 1 : inf

bar = tail $ tail inf


foo = inf !! n
  where n = myabs $ choose 0

myabs :: Int -> Int
{-@ myabs :: Int -> {v:Int | v >= 0} @-}
myabs = undefined

-- Encoding infinity.....

{-@ measure oo :: Int @-}
{-@ invariant {v:Int | (v < oo) }@-}
