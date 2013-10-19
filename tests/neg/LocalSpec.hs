module Foo where

import Language.Haskell.Liquid.Prelude (choose)


prop = if x < 0 then bar x else x
  where x = choose 0
    {-@ bar :: Nat -> Nat @-}
        bar :: Int -> Int
        bar x = x

{-@ bar :: a -> {v:Int | v = 9} @-}
bar :: a -> Int
bar _ = 8
