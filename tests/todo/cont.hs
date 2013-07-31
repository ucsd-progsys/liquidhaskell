module Cont (funkyId, funkyIds) where

------------------------------------------------------------------------------------------
{-@ funkyId :: x:Int -> {v:Int | v = x} @-}
funkyId :: Int -> Int
funkyId n = cont (\_ -> n)


{-@ cont :: forall <p :: Int -> Prop>. (() -> Int<p>) -> Int<p> @-}
cont :: (() -> Int) -> Int
cont f = f () 
------------------------------------------------------------------------------------------

{-@ funkyIds :: a -> n:Int -> {v:[a] | (len v) = n} @-}
funkyIds :: a -> Int -> [a]
funkyIds y n = conts y (\_ -> n)

{-@ conts :: forall <p :: Int -> Prop>. a -> (() -> Int<p>) -> exists z:Int<p>. {v:[a] | z = (len v)} @-}
{-@ conts :: forall <p :: Int -> Prop>. a -> (() -> Int<p>) -> {v:[a] | (p (len v))} @-}
conts :: a -> (() -> Int) -> [a] 
conts x f = clone (f ()) x 

{-@ clone :: n:Int -> a -> {v:[a] | (len v) = n} @-}
clone :: Int -> a -> [a]
clone = undefined
