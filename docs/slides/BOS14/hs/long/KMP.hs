{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module KMP (search) where

import Language.Haskell.Liquid.Prelude (liquidError)
import qualified Data.Map as M

search pat str = kmpSearch (ofList pat) (ofList str) 

-------------------------------------------------------------
-- | Do the Search ------------------------------------------
-------------------------------------------------------------

{-@ type Upto N = {v:Nat | v < N} @-} 

{-@ kmpSearch :: (Eq a) => p:Arr a -> s:Arr a -> Maybe (Upto (alen s)) @-}
kmpSearch p@(A m _) s@(A n _) = go 0 0 
  where
    t              = kmpTable p
    go i j
      | i >= n     = Nothing 
      | j >= m     = Just (i - m)
      | s!i == p!j = go (i+1) (j+1)
      | j == 0     = go (i+1) j
      | otherwise  = go i     (t!j) 


-------------------------------------------------------------
-- | Make Table ---------------------------------------------
-------------------------------------------------------------

kmpTable p@(A m _) = go t 1 0 
  where
    t              = new m (\_ -> 0)
    go t i j
      | i >= m - 1 = t

      | p!i == p!j = let i' = i + 1
                         j' = j + 1
                         t' = set t i' j'
                     in go t' i' j'           
    
      | (j == 0)   = let i' = i + 1
                         t' = set t i' 0
                     in go t' i' j
                             
      | otherwise  = let j' = t ! j
                     in go t i j' 


-------------------------------------------------------------
-- | A Pure Array -------------------------------------------
-------------------------------------------------------------

data Arr a   = A { alen :: Int
                 , aval :: Int -> a
                 }

{-@ data Arr a <p :: Int -> a -> Prop>
             = A { alen :: Nat 
                 , aval :: i:Upto alen -> a<p i>
                 }
  @-}


{-@ new :: forall <p :: Int -> a -> Prop>.
             n:Nat -> (i:Upto n -> a<p i>) -> {v: Arr<p> a | alen v = n}
  @-}
new n v = A n v

{-@ (!) :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i>
  @-}
(A _ f) ! i = f i
  
{-@ set :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i> -> {v:Arr<p> a | alen v = alen a}
  @-}
set a@(A _ f) i v = a { aval = \j -> if (i == j) then v else f j }

{-@ ofList :: xs:[a] -> {v:Arr a | alen v = len xs} @-} 
ofList xs = new n f
  where
    n     = length xs
    m     = M.fromList $ zip [0..] xs
    f i   = (M.!) m i 

{-@ map :: (a -> b) -> a:Arr a -> {v:Arr b | alen v = alen a} @-}
map f a@(A n z) = A n (f . z) 
