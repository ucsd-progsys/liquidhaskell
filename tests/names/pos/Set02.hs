module Set02 where

import Data.Set as S

{-@ add :: x:a -> [a] -> {v:[a] | S.member x (listElts v)} @-}
add :: a -> [a] -> [a]
add apple pork = apple : pork 
