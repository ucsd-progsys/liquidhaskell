{-@ LIQUID "--typeclass" @-}
module Basic where

import Prelude (Bool (True), (==))

class MyEq a where
    {-@ eq :: a -> a -> Bool @-}
    eq :: a -> a -> Bool
