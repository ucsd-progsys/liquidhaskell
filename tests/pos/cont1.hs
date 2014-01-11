module Foo () where

{-@ conts :: forall <p :: Int -> Prop>. 
             a 
          -> (() -> Int<p>) 
          -> (exists [z:Int<p>] .  {v:[a]| z = (len v)})
  @-}
     
conts :: a -> (() -> Int) -> [a] 
conts x f = clone (f ()) x 


{-@ clone :: n:Int -> a -> {v:[a] | (len v) = n} @-}
clone :: Int -> a -> [a]
clone = undefined
