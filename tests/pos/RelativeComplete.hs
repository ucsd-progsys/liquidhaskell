module Compose where

{-@ LIQUID "--no-termination" @-}

-- Here p and q of `app` will be instantiated to 
-- p , q := \v -> i <= v

main i = app (check i) i

{-@ check :: x:Int -> {v:Int | x <= v} -> () @-}
check :: Int -> Int -> ()
check = undefined


{-@ app :: forall <p :: Int -> Prop, q :: Int -> Int -> Prop>. 
           {Int<q> <: Int<p>}
           {x::Int<q> |- {v:Int| v = x + 1} <: Int<q>}
           (Int<p> -> ()) -> x:Int<q> -> () @-}
app :: (Int -> ()) -> Int -> ()
app f x = if p x then app f (x + 1) else f x


p :: a -> Bool
{-@ p :: a -> Bool @-}
p = undefined
