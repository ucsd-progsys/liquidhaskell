{-@ LIQUID "--expect-any-error" @-}
module Bag1 where

import qualified Data.Set as S
import Language.Haskell.Liquid.Bag as B

{-@ zorg :: {v:B.Bag Int | v = B.empty} @-}
zorg :: B.Bag Int
zorg = B.empty

{-@ measure elems @-}
elems :: (Ord a) => [a] -> B.Bag a
elems []     = B.empty
elems (x:xs) = B.put x (elems xs)

{-@ prop0 :: x:_ -> TT @-}
prop0 :: Int -> Bool
prop0 x = (B.get x b == 3) 
  where
    a   = elems [x, x]
    b   = B.union a a 
