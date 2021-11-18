module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)

{-@ set :: forall a <p :: x0: Int -> x1: a -> Bool, r :: x0: Int -> Bool>.
      i: Int<r> ->
      x: a<p i> ->
      a: (j: {v: Int<r> | v != i} -> a<p j>) ->
      (k: Int<r> -> a<p k>) @-}
set :: Int -> a -> (Int -> a) -> (Int -> a)
set i x a = \k -> if k == i then x else a k

{-@ get :: forall a <p :: x0: Int -> x1: a -> Bool, rap :: x0: Int -> Bool>.
             i: Int<rap> ->
             a: (j: Int<rap> -> a<p j>) ->
             a<p i> 
  @-}
get :: Int -> (Int -> a) -> a
get i a = a i

-------------------------------------------------------------------------------
---------------------------- memoization --------------------------------------
-------------------------------------------------------------------------------

{-@ measure fib :: Int -> Int @-}

{-@ type FibV = j:Int -> { v : Int | v /= 0 => (v = fib j) } @-}

type FibVV = Int -> Int 

{-@ assume axiom_fib :: i:Int -> {v: Bool | v <=> (fib i = (if i <= 1 then 1 else (fib (i-1) + fib (i-2)))) } @-}
axiom_fib :: Int -> Bool
axiom_fib = undefined

{-@ fastFib :: x:Int -> {v:Int | v = fib x} @-}
fastFib   :: Int -> Int
fastFib n = case fibMemo (\_ -> 0) n of 
	      (_, res) -> res 

{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = fib i}) @-}
fibMemo :: FibVV -> Int -> (FibVV, Int) 
fibMemo t i 
  | i <= 1    
  = (t, liquidAssume (axiom_fib i) (1 :: Int))
  
  | otherwise 
  = case get i t of   
      0 -> let (t1, n1) = fibMemo t  (i-1)
               (t2, n2) = fibMemo t1 (i-2)
               n        = liquidAssume (axiom_fib i) (n1 + n2)
           in  (set i n t2,  n)
      n -> (t, n)





















