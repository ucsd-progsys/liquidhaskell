module Fixme where

data Parity = Even | Odd

{-
  I. E ~ E
      E == E <=> 0 == 0   [v]
      
  II. case f (if ...) of { E -> O; O -> E} ~ case f (if ...) of { E -> O; O -> E}
      a) E ~ E 
          E == E
          <=> f (n1 +/- 1) == f (n2 +/- 1) 
          <=> (n1 +/- 1 - n2 -/+ 1) mod 2 == 0 
          <=> (n1 - n2) mod 2 == 0   [v]
      b,c,d) same
  
  III. E ~ case f (if ...) of { E -> O; O -> E}
      a) E ~ E  
          E == E <=> n2 mod 2 == 0 ???????????
      b) E ~ O  
          E == O <=> n2 mod 2 == 0 ????????
-}

{-@ f :: n:Int -> {v:Parity| ((v == Fixme.Even) <=> (n mod 2 == 0))
                            && ((v == Fixme.Odd) <=> (n mod 2 == 1)) } / [if n >= 0 then n else -n] @-}
f :: Int -> Parity
f 0 = Even
f n = case f (if n < 0 then n + 1 else n - 1) of
  Even -> Odd
  Odd  -> Even

{-@ relational f ~ f :: n1:_ -> _ ~ n2:_ -> _ 
                     ~~ true => ((r1 n1 == r2 n2) <=> (n1 mod 2 = n2 mod 2)) @-}