{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--no-termination"    @-}

module T1095C where

data Foo 
  = A Foo 
  | H 
  | I
    
{-@ measure size       @-}
{-@ size :: z:Foo -> {v:Nat | v = size z} @-}
size :: Foo -> Int 
size (A x) = 1 + size x 
size _     = 0 
