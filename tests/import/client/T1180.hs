{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}

module Ev where

import Peano 

pInt :: Peano -> Int 
pInt Z     = 0 
pInt (S n) = 1 + pInt n
