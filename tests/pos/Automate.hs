module Automate where

import Language.Haskell.Liquid.ProofCombinators 


fibA :: Int -> Int 
{-@ axiomatize fibA @-}
{-@ fibA :: Nat -> Nat @-}
fibA i | i <= 1 = i
      | otherwise = fibA (i-1) + fibA (i-2)


{-@ prop :: () -> {fibA 30 == 832040 } @-}
prop :: () -> Proof 
prop _ = trivial  
