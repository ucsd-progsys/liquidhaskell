{-@ LIQUID "--no-termination" @-}

module T1096_Types where

data Foo = A Foo | B 

size :: Foo -> Integer 

{-@ measure size @-}
{-@ invariant {t:Foo | 0 <= size t} @-}
{-@ size :: Foo -> {v:Integer |  0 <= v }  @-}
size (A x) = 1 + size x
size B     = 0 
