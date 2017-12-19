module BagTest where

import Language.Haskell.Liquid.Bag as B

{-@ measure bag @-}
bag :: (Ord a) => [a] -> B.Bag a
bag []     = B.empty
bag (x:xs) = B.put x (bag xs)

{-@ prop0 :: x:_ -> TT @-}
prop0 :: Int -> Bool
prop0 x = (B.get x a == 2)
  where
    a   = bag [x, x, x + 1]

{-@ prop1 :: x:_ -> TT @-}
prop1 :: Int -> Bool
prop1 x = (B.get (x + 1) a == 1)
  where
    a   = bag [x, x, x + 1]

{-@ prop2 :: x:_ -> y:_ -> TT @-}
prop2 :: Int -> Int -> Bool
prop2 x y = (a == b)
  where
    a     = bag [x, y, x]
    b     = bag [y, x, x]
