{-@ LIQUID "--reflection" @-} 

module HiddenMethod00 where

import Prelude hiding (mod, gcd)

foo :: a -> a 
foo x = x 
