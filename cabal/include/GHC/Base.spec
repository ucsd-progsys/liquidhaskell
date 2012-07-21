module spec GHC.Base where

import GHC.Prim

measure len :: forall a. [a] -> Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)

measure nully :: forall a. [a] -> Int
nully (y:ys) = 1
nully ([])   = 0

measure nonnull :: forall a. [a] -> Bool 
nonnull (y:ys) = true
nonnull ([])   = false 

assume error :: {v: String | 0 = 1} -> a
