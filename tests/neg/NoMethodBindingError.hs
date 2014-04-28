module Foo where

{-@ LIQUID "--totality" @-}

class Foo a where
  foo :: a -> a

instance Foo Int where
-- no method binding error
--
goo :: Int -> Int
goo = foo 
