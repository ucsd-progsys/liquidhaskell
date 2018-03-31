{-@ LIQUID "--no-case-expand" @-}
{-@ LIQUID "--no-termination" @-}

module Foo where

data Foo 
  = A Foo 
  | H 
  | I
    
{-@ measure size       @-}
{-@ size :: z:Foo -> {v:Nat | v = size z} @-}
size :: Foo -> Int 
size (A x) = 1 + size x 
size _     = 0 
