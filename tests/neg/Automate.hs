module Automate where

{-@ LIQUID "--automatic-instances=smtinstances" @-}

import Language.Haskell.Liquid.ProofCombinators 


fibA :: Int -> Int 
{-@ axiomatize fibA @-}
{-@ fibA :: Nat -> Nat @-}
fibA i | i <= 1 = i
      | otherwise = fibA (i-1) + fibA (i-2)


fibR :: Int -> Int 
{-@ reflect fibR @-}
{-@ fibR :: Nat -> Nat @-}
fibR i | i <= 1 = i
      | otherwise = fibR (i-1) + fibR (i-2)


{-@ prop :: () -> {fibA 30 == 832040 } @-}
prop :: () -> Proof 
prop _ = trivial  

-- This is unsafe because it is actually false 

{-@ propUNSAFE :: () -> {fibA 30 == 832042 } @-}
propUNSAFE :: () -> Proof 
propUNSAFE _ = trivial  


-- This is unsafe because the reflected fibR (vs. axiomatized fibA)
-- does not create an SMT axiom
{-@ propR :: () -> {fibR 30 == 832040 } @-}
propR :: () -> Proof 
propR _ = trivial  