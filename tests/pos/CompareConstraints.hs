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
{-

-----------------


data Dyn = Int Int | String String | Bool Bool 
type Key = String
data Box = Record Key Dyn

emp :: Box
emp = undefined

class Value v where
  toDyn   :: v -> Dyn
  fromDyn :: Dyn -> v
 
put :: (Value v) => Key -> v -> Box -> Box
put k v b = insert k b (toDyn v) 

get :: (Value v) => Box -> Key -> v
get = undefined

rj  :: Box
rj  = put "name"     "Ranjit" 
    $ put "age"      10
    $ put "sleeping" True
    $ emp 

out = "My name is " ++ get rj "name"


sumXY box x y = get box x + get box y

-}
















 
