module Foo where

import Language.Haskell.Liquid.Prelude

prop :: Bool
prop = undefined

{-@ app :: forall <p :: a -> Prop, q :: a -> Prop>. 
   {x:a<q> -> a<p> -> {v:a | v <= x}}
   {a<q> -> a<p>}
   Num a => (a<p> -> b) -> a<q> -> b @-}
app :: Num a => (a -> b) -> a -> b
app f x = if prop then app f (x+1) else f x


{-@ check :: Ord a => x:a ->  {v:a | x <= v} -> () @-}
check :: Ord a => a ->  a -> ()
check x y | x <= y = ()
          | otherwise = liquidError ""

main i = app (check i) i       