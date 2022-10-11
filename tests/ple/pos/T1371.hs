{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}

module T1371 where

data Thing  
  = N Int 
  | Op Thing Thing 


{- THE BELOW GENERATES A DIVERGING FUNCTION 'define' that KILLS PLE 

{-@ reflect foo @-}
{-@ foo :: _ -> _ -> { 1 + 2 == 3 } @-}
foo :: Thing -> Thing -> Thing
foo (N n)      (Op e1 e2) = Op e1 (foo (N n) e2)
foo (Op e1 e2) x          = Op e1 (foo e2 x)
-- foo e          _          = e 

-} 

{-@ reflect bar @-}

{-@ bar :: _ -> _ -> { 1 + 2 == 3 } @-}
bar :: Thing -> Thing -> Thing
bar (N n)      (Op e1 e2) = Op e1 (bar (N n) e2)
bar (Op e1 e2) x          = Op e1 (bar e2 x)
bar e          _          = e 
