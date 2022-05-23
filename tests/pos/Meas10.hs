module Meas10 where

import qualified Data.Set as S 

import Language.Haskell.Liquid.Prelude

{-@ myrev :: xs:[a] -> {v:[a] | listElts v = listElts xs} @-}
myrev :: [a] -> [a]
myrev xs = go [] xs 
   where 
      go acc []     = acc
      go acc (y:ys) = go (y:acc) ys

-- WHY DOES THIS JUST NOT GET ANY MEANINGFUL TYPE?
{-@ goo :: xs:[a] -> ys:[a] -> {v:[a] | listElts v = S.union (listElts xs) (listElts ys) } @-}
goo :: [a] -> [a] -> [a]
goo acc []     = acc
goo acc (y:ys) = unsafeError "foo" -- goRev (y:acc) ys

{-@ emptySet :: a -> {v:[b] | listElts v == S.empty } @-}
emptySet :: a -> [b]
emptySet x = []
