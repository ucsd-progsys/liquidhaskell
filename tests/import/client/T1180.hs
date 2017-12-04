{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}

module Ev where

import Peano 

test :: Peano -> Int 
test Z     = 0 
test (S n) = test n 

