{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module KMP (search) where

import Language.Haskell.Liquid.Prelude (liquidError)

search pat str = kmpSearch (ofList pat) (ofList str) 

-------------------------------------------------------------
-- | Do the Search ------------------------------------------
-------------------------------------------------------------

kmpSearch p@(A m _) s@(A n _) = go 0 0 
  where
    t              = kmpTable p
    go i j
      | j >= m     = i - m
      | i >= n     = (-1)
      | s!i == p!j = go (i+1) (j+1)
      | j == 0     = go (i+1) j
      | otherwise  = go i     (t!j) 


-------------------------------------------------------------
-- | Make Table ---------------------------------------------
-------------------------------------------------------------

{-@ kmpTable :: (Eq a) => p:Arr a -> {v:DArr Nat | alen v = alen p} @-}
kmpTable p@(A m _) = go 1 0 t
  where
    t              = new m (\_ -> 0)
    go i j t
      | i >= m - 1 = t

      | p!i == p!j = let i' = i + 1
                         j' = j + 1
                         t' = wipe $ set t i' j'
                     in go i' j' t'           
    
      | (j == 0)   = let i' = i + 1
                         t' = wipe $ set t i' 0
                     in go i' j t'
                             
      | otherwise  = let j' = t ! j
                     in go i j' t 

{-@ wipe :: a:DArr Nat -> {v:DArr Nat | alen v = alen a} @-}
wipe :: Arr Int -> Arr Int
wipe = undefined


{-@ type DArr a = Arr<{\k v -> v <= k}> a @-}
{-@ type Upto N = {v:Nat | v < N} @-} 

-------------------------------------------------------------
-- | An Array type ------------------------------------------
-------------------------------------------------------------

data Arr a = A { alen :: Int
               , aval :: Int -> a
               }

{-@ data Arr a <rng :: Int -> a -> Prop>
      = A { alen :: Nat 
          , aval :: i:Upto alen -> a<rng i>
          }
  @-}


{-@ new :: forall <p :: Int -> a -> Prop>.
             n:Nat -> (i:Upto n -> a<p i>) -> {v: Arr<p> a | alen v = n}
  @-}
new n v = A { alen = n
            , aval = \i -> if (0 <= i && i < n)
                             then v i
                             else liquidError "Out of Bounds!"
            }

{-@ (!) :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i>
  @-}

(A _ f) ! i = f i
  
{-@ set :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i> -> {v:Arr<p> a | alen v = alen a}
  @-}
set a@(A _ f) i v = a { aval = \j -> if (i == j) then v else f j }


{-@ ofList :: xs:[a] -> {v:Arr a | alen v = len xs} @-} 
ofList :: [a] -> Arr a
ofList = undefined

