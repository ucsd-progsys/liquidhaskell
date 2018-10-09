-- TAG: classes 
-- TAG: bounds 

{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--higherorder"       @-}

module STClient where

import STLib 

--------------------------------------------------------------------------------

{-@ fresh :: forall <pre :: Int -> Bool>.
                    { zoo::Int |- Int<pre> <: {v:Int | 0 <= v} }
                    ST <pre, {\rv v -> ( 0 <= rv && rv + 1 = v )}> Int (Int<pre>)
  @-}

{- fresh :: ST <{\v -> (0 <= v)}, {\rv v -> ( 0 <= rv && rv + 1 = v )}> Int Nat @-}
fresh :: ST Int Int
fresh = S (\n -> (n, n+1))

--------------------------------------------------------------------------------

{-@ incr0 :: ST <{\v -> (0 <= v)}, {\rv v -> (0 <= rv && 1 <= v)}> Int Int @-}
incr0 :: ST Int Int
incr0 = do
  n <- fresh
  return n

{-@ incr1 :: ST <{\v -> (0 <= v)}, {\rv v -> (0 <= rv && 1 <= v)}> Int Int @-}
incr1 :: ST Int Int
incr1 = fresh >>= return

{-@ incr2 :: ST <{\v -> (0 == v)}, {\rv v -> (4 == v)}> Int Int @-}
incr2 :: ST Int Int
incr2 = do
  n0 <- fresh
  n1 <- fresh
  n2 <- fresh
  n3 <- fresh
  return (checkEq 3 n3)

{-@ checkEq :: x:Int -> y:{Int | y = x} -> {v:Int | v = y} @-}
checkEq :: Int -> Int -> Int
checkEq x y = y
