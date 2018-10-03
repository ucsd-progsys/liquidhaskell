module FunClashLib (blob) where

import FunClashLibLib 

{-@ blob :: Nat -> Nat @-} 
blob :: Int -> Int 
blob = incr 

