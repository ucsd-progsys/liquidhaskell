{-@ LIQUID "--no-termination" @-}

module KMP where

import Prelude hiding (init)


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

kmpTable p    = go 1 0 t
  where
    m         = alen p
    t         = new m (\_ -> 0)
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

-------------------------------------------------------------
-- | An Array type ------------------------------------------
-------------------------------------------------------------

data Arr a = A { alen :: Int
               , aval :: Int -> a
               }


new     :: Int -> (Int -> a) -> Arr a
new n v = A { alen = n
            , aval = \i -> if (0 <= i && i < n) then v i else error "Out of Bounds!"
            }

(!)   :: Arr a -> Int -> a
a ! i = aval a i
  
set :: Arr a -> Int -> a -> Arr a
set a i v = a { aval = \j -> if (i == j) then v else (a ! j) }


