module LocalSpec () where

import Language.Haskell.Liquid.Prelude (choose)


prop = if x > 0 then bar x else foo x
  where x = choose 0
    {-@ Local bar :: Nat -> Nat @-}
        bar :: Int -> Int
        bar x = x
    {-@ Local foo :: Nat -> Nat @-}
        foo :: Int -> Int
        foo x = x

{-@ bar :: a -> {v:Int | v = 9} @-}
bar :: a -> Int
bar _ = 9
