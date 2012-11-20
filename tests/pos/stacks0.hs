module StackSet where

import Data.Set (Set(..)) 

{-@ data LL a = Nil | Cons { head :: a 
                           , tail :: {v: LL a | not (Set_mem head (elts v))  } } 
  @-}


{-@ measure elts :: LL a -> (Set a) 
    elts (Nil)       = {v | (Set_emp v)}
    elts (Cons x xs) = {v | v = (Set_cup (Set_sng x) (elts xs)) }
  @-}

data LL a = Nil | Cons { head :: a, tail :: LL a }

x0, x1, x2 :: Int
x0  = 0
x1  = 1
x2  = 2

ll2 = Cons x2 Nil
ll1 = Cons x1 ll2
-- ll0 = Cons x0 ll1

