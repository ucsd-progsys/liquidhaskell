
{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--extensionality"  @-}
module Append where

import Prelude hiding (id)

import Proves

{- f and g are declare to be literals see #746
f :: a -> b 
f = undefined 
g :: a -> b 
g = undefined 
-}


{-@ axiomatize id @-}
id :: a -> a
id x = x

{- 
{-@ fmap_id :: () -> {\r:a -> r == \r:a -> (id r) } @-}
fmap_id :: () ->  Proof
fmap_id _ = fun_eq (\r -> r) (\r -> (id r)) (\x -> x ==! id x *** QED)
-}

{-@ fmap_id' 
  :: x:(r -> a)
  -> {v:Proof | (\r:r -> id (x r)) ==  (\r:r -> (x r) ) } @-}
fmap_id' :: (r -> a) ->  Proof
fmap_id' x
   =   fun_eq (\rrr1 -> x rrr1) (\rrr2 -> id (x rrr2)) (\r -> x  r ==. id (x r) *** QED)



{-@ fun_eq :: f:(a -> b) -> g:(a -> b) 
   -> (x:a -> {f x == g x}) -> {f == g} 
  @-}   
fun_eq :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof   
fun_eq = undefined 




