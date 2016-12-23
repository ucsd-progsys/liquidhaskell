module ListElem (listElem) where

import Data.Set

{-@ listElem :: (Eq a)
             => y:a
             -> xs:[a]
             -> {v:Bool | v <=> Set_mem y (listElts xs)}
  @-}

listElem :: (Eq a) => a -> [a] -> Bool
listElem _ []      = False
listElem y (x:_xs)
  | x == y         = True
  | otherwise      = True -- listElem y xs
