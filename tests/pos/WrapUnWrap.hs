{-@ LIQUID "--totality"     @-}
{-@ LIQUID "--higherorder"  @-}
{-@ LIQUID "--exactdc"      @-}
module Data.Foo where


import Language.Haskell.Liquid.ProofCombinators

data    Prod1 a = Prod1 {unprod1 :: a }
{-@ data Prod1 a = Prod1 {unprod1 :: a } @-}

prod1Theorem :: Prod1 a -> Proof 
{-@ prod1Theorem :: x:Prod1 a -> {x == Prod1 (unprod1 x)} @-}
prod1Theorem (Prod1 _) = trivial 