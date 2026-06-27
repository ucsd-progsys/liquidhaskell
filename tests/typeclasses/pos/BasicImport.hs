{-@ LIQUID "--typeclass" @-}
module BasicImport where

import Prelude (Bool (True), (==))
import Basic

class MyEq a => MyVEq a where
    {-@ lawRefl' :: v:a -> {eq v v == True} @-}
    lawRefl' :: a -> ()
