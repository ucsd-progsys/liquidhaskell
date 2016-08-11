{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--totality"         @-}
{-@ LIQUID "--exact-data-cons"  @-}
{-@ LIQUID "--alphaequivalence" @-}
{-@ LIQUID "--betaequivalence"  @-}
{-@ LIQUID "--normalform"       @-}

module MonadReader where
import Proves



{-

equivalence via Debruijin representation breaks here, as a lambda is inserted
verification requires normal form equality axioms

instance taken from MonadReader.associativity

-}


foo :: (a -> c) -> Proof 
{-@ foo :: f:(a ->  c) 
  -> {(\x:a -> (\y:b -> f x) )  == (\x:a -> (\z:c -> (\y:b -> f x))(f x) )   } @-} 
{- foo :: f:(a ->  c) 
  -> {(\x:a -> (\y:a -> f y) )  == (\x:a -> (\z:c -> (\y:a -> f x))(f x) )   } @-} 
foo _ = simpleProof 