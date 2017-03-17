module Automate where

{-@ LIQUID "--automatic-instances=smtinstances" @-}

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

{-@ prop :: () -> {fibA 30 == 832040 } @-}
prop :: () -> Proof 
prop _ = trivial  
