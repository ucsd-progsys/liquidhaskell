{-# LANGUAGE GADTs #-}

{-@ LIQUID "--noadt" @-}

module T1180 where

import PeanoLib

pInt :: Peano -> Int 
pInt Z     = 0 
pInt (S n) = 1 + pInt n
