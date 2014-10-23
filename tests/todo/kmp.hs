{-@ LIQUID "--no-termination" @-}

{-@ LIQUID "-i ."             @-}

module KMP where

import Array

-------------------------------------------------------------
-- | Do the Search ------------------------------------------
-------------------------------------------------------------

kmpSearch p s          = go 0 0 
  where
    t                  = kmpTable p
    m                  = alen p
    n                  = alen s

    go i j
      | j < m && i < n = go' i j
      | otherwise      = if (j >= m) then i-m else (-1)
    
    go' i j
      | s!i == p!j     = go (i+1) (j+1)
      | j == 0         = go (i+1) j
      | otherwise      = go i     (t!j) 
    


-------------------------------------------------------------
-- | Make Table ---------------------------------------------
-------------------------------------------------------------

kmpTable p               = go 1 0 t
  where
    m                    = alen p
    t                    = new m (\_ -> 0)
    go i j t
      | (i < m - 1)      = go' i j t
      | otherwise        = t

    go' i j t
      | (p ! i == p ! j) = let i' = i + 1
                               j' = j + 1
                               t' = set t i' j'
                           in go i' j' t'           
    
      | (j == 0)         = let i' = i + 1
                               t' = set t i' 0
                           in go i' j t'
                             
      | otherwise        = let j' = t ! j
                           in go i j' t 
