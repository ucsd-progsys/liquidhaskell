{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--exact-data-cons"  @-}
{-@ LIQUID "--alphaequivalence" @-}
{-@ LIQUID "--betaequivalence"  @-}
{-@ LIQUID "--normalform"       @-} 

module NormalForm where
import Language.Haskell.Liquid.ProofCombinators

{-

equivalence via Debruijin representation breaks here, 
as a lambda is inserted, verification requires normal 
form equality axioms. 
instance taken from MonadReader.associativity

-}


foo :: (a -> c) -> Proof 
{-@ foo :: f:(a ->  c) 
  -> {(\x:a -> (\y:b -> f x))  == (\x:a -> (\z:c -> (\y:b -> f x)) (f x)) } @-} 
foo _ = trivial  

