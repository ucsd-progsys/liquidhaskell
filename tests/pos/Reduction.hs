{-@ LIQUID "--higherorder"    @-}

module Reductions where

{-@ reduction :: forall<p :: a -> Bool -> Bool>. 
                 f:(a -> a) 
              -> (x:a -> Bool<p x>) 
              -> y:a -> Bool<p (f y)>  @-}
reduction :: (a -> a) -> (a -> Bool) -> a -> Bool
reduction f thm y = thm (f y)              

