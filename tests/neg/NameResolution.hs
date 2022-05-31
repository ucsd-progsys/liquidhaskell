{-@ LIQUID "--expect-any-error" @-}
module NameResolution where

import Prelude hiding ((==), (++))
import Language.Haskell.Liquid.Equational 


{-@ bar :: () -> Int @-}
bar :: () -> Int
bar _
  =   1 
  ==. 2 


{-@ (==..) :: x:a -> y:{a | x == y} -> {v:a | v == y && v == x} @-}
(==..) :: a -> a -> a 
_ ==.. x = x

{-@ foo :: () -> Int @-}
foo :: () -> Int
foo _
  =   1 
  ==.. 2 


{-@ (++) :: a -> a -> a @-}
(++) :: a -> a -> a 
x ++ _ = x 
