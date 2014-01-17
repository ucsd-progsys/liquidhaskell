module ListElem () where

import Data.Set

{-@ listElem :: (Eq a) 
             => y:a 
             -> xs:[a]
             -> {v:Bool | (Prop(v) <=> Set_mem(y, (listElts(xs))))} 
  @-}

listElem :: (Eq a) => a -> [a] -> Bool
listElem _ []     = False
listElem y (x:xs) | x == y    = True
                  | otherwise = listElem y xs

