module GenTerm () where

import Prelude hiding (reverse)

foo :: Int -> Int -> Int
{-@ foo :: n:Nat -> m:Nat -> Nat /[n+m] @-}

foo n m 
  | cond 1 = 0
  | cond 2 && n > 1 = foo (n-1) m
  | cond 3 && m > 2 = foo (n+1) (m-2)
 
{-@ cond :: Int -> Bool @-}
cond :: Int -> Bool
cond _ = undefined


data L a = N | C a (L a)

{-@ data L [llen] @-}

{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v: L a | (llen v) >= 0} @-}

{-@ reverse :: xs: L a -> ys : L a -> L a / [(llen ys)] @-}
reverse :: L a -> L a -> L a
reverse xs N = xs
reverse xs (C y ys) = reverse (C y xs) ys

merge :: Ord a => L a -> L a -> L a 
{-@ merge :: Ord a => xs:L a -> ys:L a -> L a /[(llen xs) + (llen ys)]@-}
merge (C x xs) (C y ys) | x > y     = C x $ merge xs (C y ys) 
                        | otherwise = C y $ merge (C x xs) ys
