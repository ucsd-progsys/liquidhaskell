{-# LANGUAGE ScopedTypeVariables #-}

module Term0 () where 

import Prelude hiding (sum)

{-@ sum :: Nat -> Nat @-}
sum   :: Int -> Int
sum 0 = 0
sum n = n + sum (n-1)

{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int 
fib 0 = 1
fib 1 = 1 
fib n = fib (n-1) + fib (n-2)

{-@ sumUp :: Nat -> Nat @-}
sumUp :: Int -> Int
sumUp n  = go n 0 0
  where 
    go (d :: Int) acc i
      | i < n     = go (d - 1) (acc + i) (i + 1) 
      | otherwise = acc

{-@ qualif Diff(v:Int, x:Int, y:Int): v = x - y @-} 

{-@ nonTerm :: Nat -> Nat @-}
nonTerm :: Int -> Int
nonTerm n = nonTerm (n+1)

{-@ Lazy nonTerm @-}

