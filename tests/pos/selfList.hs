module Foo () where

import Data.Set (Set(..)) 

{-@ include <selfList.hquals> @-}

{-@ invariant {v0:[{v: a | (Set_mem v (listElts v0))}] | true } @-}

{-@ type IList a  = {v0: [{v:a | (Set_mem v (listElts v0))}] | true } @-}

{-@ moo :: [a] -> IList a @-}
moo []     = [] 
moo (_:xs) = xs

goo []     = [] 
goo (_:xs) = xs

{-@ poo :: IList Int @-}
poo = goo xs
  where 
    xs :: [Int]
    xs = [2,1,3,2]


