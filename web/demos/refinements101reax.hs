module Refinements101Reax where


--------------------------------------------------------------------
----------- Part I: Relating Inputs and Outputs --------------------
--------------------------------------------------------------------

{-@ f :: Int -> Int @-}
f x | abz x == 0 = 3
    | otherwise  = 3 `divide` x

-- This specification is TOO WEAK nothing about the relationship between
-- the input and output
-- abz :: Int -> {v: Int | 0 <= v }

-- This specification is VERY STRONG in that it describes the EXACT
-- behavior of abz, rarely possible for non-trivial functions
-- abz :: x:Int -> {v:Int | v = (if (x > 0) then x else (0 - x))}

-- This specification is JUST RIGHT 

{-@ abz :: x:Int -> {v:Int | ((0 <= v) && ((v = 0) <=> (x = 0))) } @-}
abz               :: Int -> Int
abz n | 0 < n     = n
      | otherwise = 0 - n

-- | A *divide* function that *only accepts* non-zero denominators

{-@ divide :: Int -> {v: Int | v /= 0 } -> Int @-}
divide     :: Int -> Int -> Int
divide n 0 = error' "divide by zero"
divide n d = n `div` d

-- | A wrapper around the usual `error` function

{-@ error' :: {v: String | false } -> a  @-}
error'     :: String -> a
error'     = error


--------------------------------------------------------------------
----------- Part II: Telling a Fib ---------------------------------
--------------------------------------------------------------------

-- | This is UNSAFE for 2 reasons. Can you fix it?

{-@ fib :: n:Int -> { b:Int | (n >= 0 && b >= n) } @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

-- | This is still UNSAFE, because its not true, since `fib' 2 == 1`

{-@ fib' :: n:{v:Int | v >= 0} -> {b:Int | (n >= 0 && b >= n) } @-}
fib' :: Int -> Int
fib' 0 = 0
fib' 1 = 1
fib' n = fib (n-1) + fib (n-2)

-- | Third time's a charm! Note we have strengthened the output type so
-- that it is inductive...

{-@ fibOK :: n:Int -> {b:Int | ((b >= n) && (b >= 1))} @-}
fibOK :: Int -> Int
fibOK 0 = 1
fibOK 1 = 1
fibOK n = fibOK (n-1) + fibOK (n-2)

