module Automate where

{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-
fuel 0 for fib up to 1 
fuel 1 for fib up to 2
fuel 2 for fib up to 4
fuel 3 for fib up to 8
...
-}


{-@ LIQUID "--fuel=4" @-}

import Language.Haskell.Liquid.ProofCombinators 


fibA :: Int -> Int 
{-@ axiomatize fibA @-}
{-@ fibA :: Nat -> Nat @-}
fibA i | i <= 1 = i
      | otherwise = fibA (i-1) + fibA (i-2)


fibUp :: Int -> Proof 
{-@ fibUp :: i:Nat -> {fibA i <= fibA (i+1)} @-}
fibUp i 
 | i <= 2    = trivial
 | otherwise = fibUp (i-1) &&& fibUp (i-2) *** QED 

{-@ prop :: () -> {fibA 6 == 8 } @-}
prop :: () -> Proof 
prop _ = trivial  
