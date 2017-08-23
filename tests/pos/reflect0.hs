{-@ LIQUID "--higherorder"     @-}

module FunctionAbstraction where

{-@ fib :: n:Nat -> Nat @-}
{-@ reflect fib @-}
fib :: Int -> Int
fib n
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)


{-@ goo :: Nat -> Nat @-}
goo :: Int -> Int
goo x = fib x
