module Bag1 where

import qualified Data.Set as S
import Language.Haskell.Liquid.Bag as B

{-@ zorg :: {v:Bag Int | v = B.empty} @-}
zorg :: B.Bag Int
zorg = B.empty

{-@ measure elems @-}
{-@ elems :: Ord a => [a] -> Bag a @-}
elems :: (Ord a) => [a] -> B.Bag a
elems []     = B.empty
elems (x:xs) = B.put x (elems xs)

{-@ prop0 :: x:_ -> TT @-}
prop0 :: Int -> Bool
prop0 x = (B.get x b == 4)
  where
    a   = elems [x, x]
    b   = B.union a a

{-@ prop1 :: x:_ -> TT @-}
prop1 :: Int -> Bool
prop1 x = (B.get x c == 3)
  where
    a   = elems [x, x]
    b   = elems [x, x, x]
    c   = B.unionMax a b

{-@ prop2 :: x:_ -> TT @-}
prop2 :: Int -> Bool
prop2 x = (B.get x c == 2)
  where
    a   = elems [x, x]
    b   = elems [x, x, x]
    c   = B.interMin a b

{-@ prop3 :: x:_ -> y:_ -> TT @-}
prop3 :: Int -> Int -> Bool
prop3 x y = (B.sub a b == True)
  where
    a   = elems [x, x]
    b   = elems [x, x, x, y]
