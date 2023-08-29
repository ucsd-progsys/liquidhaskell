{-@ LIQUID "--expect-any-error" @-}
module Bag where

import qualified Data.Set                    as S
import           Language.Haskell.Liquid.Bag as B

{-@ zorg :: {v:Bag Int | v = B.empty} @-}
zorg :: B.Bag Int
zorg = B.empty

{-@ measure elems @-}
elems :: (Ord a) => [a] -> B.Bag a
elems []     = B.empty
elems (x:xs) = B.put x (elems xs)

{-@ prop0 :: x:_ -> TT @-}
prop0 :: Int -> Bool
prop0 x = (B.get x a == 3)
  where
    a   = elems [x, x, x + 1]

{-@ prop2 :: x:_ -> y:_ -> TT @-}
prop2 :: Int -> Int -> Bool
prop2 x y = (a == b)
  where
    a     = elems [x, y, x]
    b     = elems [y, x, x]
