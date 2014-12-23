module Foo where

import Language.Haskell.Liquid.Prelude


{-@ mycmp :: forall <p :: a -> Prop, q :: a -> Prop>. 
           {x:a<p> -> y:a<q> -> a -> {v:a | x <= y} } 
           Ord a => 
           [a<p>] -> [a<q>] -> Bool @-}
mycmp :: Ord a => [a] -> [a] -> Bool
mycmp (x:_) (_:y:_) = liquidAssert (x <= y) True


{-@ mycmp' :: forall <p :: a -> Prop, q :: a -> Prop>. 
           {x:a<p> -> y:a<q> -> a -> {v:a | x <= y} } 
           Ord a => 
           a<p> -> a<q> -> Bool @-}
mycmp' :: Ord a => a -> a -> Bool
mycmp' x y = liquidAssert (x <= y) True

bar :: Bool
bar = let w = choose 0 in 
      let x = w + 1 in 
      let y = w - 1 in 
      let z = w + 2 in 
      mycmp [x, y, x] [z, x, z]


bar' :: Bool
bar' = let w = choose 0 in 
      let x = w + 1 in 
      let y = w - 1 in 
      let z = w + 2 in 
      mycmp' x z     