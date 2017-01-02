module Language.Haskell.Liquid.Reduction where

import Language.Haskell.Liquid.ProofCombinators

{-@ LIQUID "--higherorder" @-}

{-@ reduction :: forall<p :: a -> Proof -> Prop>. 
                 f:(b -> a) 
              -> (x:a -> Proof<p x>) 
              -> (y:b -> Proof<p (f y)>) @-}
reduction :: (b -> a) -> (a -> Proof) -> (b -> Proof)
reduction f thm y = thm (f y)


{-@ reduction2 :: forall<p :: a -> a -> Proof -> Prop >. 
                  f:(b -> a) 
               -> (x1:a -> x2:a -> Proof<p x1 x2>) 
               -> (y1:b -> y2:b-> Proof<p (f y1) (f y2)>) @-}
reduction2 :: (b -> a) -> (a -> a -> Proof) -> (b -> b -> Proof)
reduction2 f thm y1 y2  = thm (f y1) (f y2)
