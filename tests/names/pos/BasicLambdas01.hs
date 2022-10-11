{-@ LIQUID "--reflection"      @-}

module BasicLambdas01 where

import Prelude hiding (id)

import Language.Haskell.Liquid.ProofCombinators 


{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ fmap_id' 
     :: x:(r -> a)
     -> {v:Proof | (\roo:r -> id (x roo)) ==  (\moo:r -> (x moo) ) } @-}
fmap_id' :: (r -> a) ->  Proof
fmap_id' x
   =   fun_eq (\rrr1 -> x rrr1) (\rrr2 -> id (x rrr2)) (\r -> x  r === id (x r) *** QED)



{-@ fun_eq :: f:(a -> b) -> g:(a -> b) 
      -> (x:a -> {f x == g x}) -> {f == g} 
  @-}   
fun_eq :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof   
fun_eq = undefined 
