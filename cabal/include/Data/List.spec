module spec Data.List where

measure len :: forall a. [a] -> Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)

measure nully :: forall a. [a] -> Int
nully (y:ys) = 1
nully ([])   = 0

measure nonnull :: forall a. [a] -> Bool 
nonnull (y:ys) = true
nonnull ([])   = false 

assume Prelude.length :: forall a. x: [a] -> { v: Int | v = len(x) }
