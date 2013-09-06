module Fixme where

import Language.Haskell.Liquid.Prelude

{-@ Lazy inf @-}
{-@ inf :: {v:[Int] | ((len v) > max_int)} @-}
inf :: [Int]
inf = 1 : inf

bar = tail $ tail inf


foo = inf !! n
  where n = myabs $ choose 0

myabs :: Int -> Int
{-@ myabs :: Int -> {v:Int | v >= 0} @-}
myabs = undefined

-- Encoding infinity.....

{-@ measure max_int :: Int @-}
{-@ invariant {v:[a] | ((len v) > 0) }@-}
{-@ invariant {v:Int | (v < max_int) }@-}
