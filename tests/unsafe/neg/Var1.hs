{-# LIQUID "--Werror" #-}

module Var1 where

h :: ()
h = let x = undefined in x
