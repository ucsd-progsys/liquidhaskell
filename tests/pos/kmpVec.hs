{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module KMP (search) where

import Language.Haskell.Liquid.Prelude (liquidError)
import Data.Vector
import Data.Vector.Mutable (write)
import Prelude hiding (length, replicate)

{-@ type Idx X = {v:Nat | v < vlen X} @-}


search pat str = kmpSearch (fromList pat) (fromList str) 

-------------------------------------------------------------
-- | Do the Search ------------------------------------------
-------------------------------------------------------------

kmpSearch p s      = go 0 0 
  where
    t              = kmpTable p
    m              = length p
    n              = length s
    go i j
      | j >= m     = i - m
      | i >= n     = (-1)
      | s!i == p!j = go (i+1) (j+1)
      | j == 0     = go (i+1) j
      | otherwise  = go i     (t!j) 


-------------------------------------------------------------
-- | Make Table ---------------------------------------------
-------------------------------------------------------------

{-@ kmpTable :: (Eq a) => p:Vector a -> {v:Vector Nat | vlen v = vlen p} @-}
kmpTable p         = go 1 0 t
  where
    m              = length p
    t              = replicate m 0 
    go i j t
      | i >= m - 1 = t

      | p!i == p!j = let i' = i + 1
                         j' = j + 1
                         t' = set t i' j'
                     in go i' j' t'           
    
      | (j == 0)   = let i' = i + 1
                         t' = set t i' 0
                     in go i' j t'
                             
      | otherwise  = let j' = t ! j
                     in go i j' t 


{-@ type Upto N = {v:Nat | v < N} @-} 

{-@ set :: a:Vector a -> i:Idx a -> a -> {v:Vector a | vlen v = vlen a} @-}
set :: Vector a -> Int -> a -> Vector a
set = undefined

