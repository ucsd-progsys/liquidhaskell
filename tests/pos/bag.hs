module BagTest where

import qualified Data.Set as S
import Language.Haskell.Liquid.Bag as B

{-@ measure elems @-}
elems :: (Ord a) => [a] -> B.Bag a
elems []     = B.empty
elems (x:xs) = B.put x (elems xs)

{-@ prop0 :: x:_ -> TT @-}
prop0 :: Int -> Bool
prop0 x = (B.get x a == 2)
  where
    a   = elems [x, x, x + 1]

{-@ prop1 :: x:_ -> TT @-}
prop1 :: Int -> Bool
prop1 x = (B.get (x + 1) a == 1)
  where
    a   = elems [x, x, x + 1]

{-@ prop2 :: x:_ -> y:_ -> TT @-}
prop2 :: Int -> Int -> Bool
prop2 x y = (a == b)
  where
    a     = elems [x, y, x]
    b     = elems [y, x, x]
