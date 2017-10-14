{-# LANGUAGE RebindableSyntax #-}

module Rebind () where 

import Prelude hiding ((>>), (>>=), return)

(>>)   = plus
return = id 

{-@ plus :: x:Nat -> y:Nat -> {v:Nat | v = x + y} @-}
plus :: Int -> Int -> Int 
plus x y = x + y 

{-@ test :: {v:Nat | v = 10} @-}
test = do 
  1
  2
  3
  4

