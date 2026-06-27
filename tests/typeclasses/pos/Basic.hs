{-@ LIQUID "--typeclass" @-}
module Basic where

import Prelude (Bool (True), (==))

class MyEq a where
    {-@ eq :: a -> a -> Bool @-}
    eq :: a -> a -> Bool

-- class MyEq a => VEq a where
--     {-@ lawRefl :: v:a -> {eq v v == True} @-}
--     lawRefl :: a -> ()
