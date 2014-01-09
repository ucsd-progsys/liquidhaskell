module GenTerm () where

foo :: Int -> Int -> Int
{-@ foo :: n:Nat -> m:Nat -> Nat /[n+m] @-}

foo n m 
  | cond 1 = 0
  | cond 2 && n > 1 = foo (n-1) m
  | cond 3 && m > 2 = foo (n+10) (m-2)
 
{-@ cond :: Int -> Bool @-}
cond :: Int -> Bool
cond _ = undefined
