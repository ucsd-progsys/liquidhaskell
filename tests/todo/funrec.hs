module Foo where

data F a = F { f :: Int -> a }

{-@ data F a = F { f :: Nat -> a } @-}
