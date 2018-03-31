{-@ LIQUID "--no-case-expand" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection" @-}

module Foo where

data Foo 
  = A Foo 
  | H 
  | I
    
{-@ measure size       @-}
{-@ size :: Foo -> Nat @-}
size :: Foo -> Int 
size (A x) = 1 + size x 
size _     = 0 
  
{-@ reflect zing @-}
zing :: Foo -> Int 
zing (A z) = zing z 
zing _     = 10 

-- zing H     = 20 
-- zing I     = 30