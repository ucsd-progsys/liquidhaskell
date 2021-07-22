{-@ LIQUID "--reflection" @-}
module Data.Endo where

{-@ data Endo a = Endo {appEndo :: a -> a} @-}
data Endo a = Endo {appEndo :: a -> a}
