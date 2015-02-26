module Intro where



{-@ foo :: forall <p :: a -> Prop, q :: a -> Prop>. 
           {x::a<p> |- a<q> <: {v:a | x > v} }
           {v:[a<p>] | len v = 1 } -> a<q> ->  a<p> @-}
foo :: Ord a => [a] -> a ->  a
foo [x] y | x > y = x
foo _   _         = crash ""


{-@ crash :: {v:String | false} -> a @-}
crash = error