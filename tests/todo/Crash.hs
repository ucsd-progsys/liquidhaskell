module Foo where

{-@ assume foo :: a -> a @-}
foo :: a -> a
foo f = foo f  
