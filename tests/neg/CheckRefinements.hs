{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

{-@ LIQUID "--check-refinements" @-}
{-@ LIQUID "--reflection" @-}

module CheckRefinements where

{-@ reflect positive @-}
{-@ positive :: {v:Int | v > 0} -> Bool @-}
positive :: Int -> Bool
positive x = x > 0

-- The ordinary sort checker accepts @positive x@.  Refinement checking must
-- reject it because @x@ does not satisfy @positive@'s refined precondition.
{-@ bad :: x:Int -> {v:Bool | positive x} @-}
bad :: Int -> Bool
bad _ = undefined 

data List a = Nil | Cons a (List a)

{-@ measure mylen @-}
{-@ mylen :: List a -> Nat @-}
mylen :: List a -> Int
mylen Nil = 0
mylen (Cons _ xs) = 1 + mylen xs

{-@ reflect get @-}
{-@ get :: n:{Int | 0 <= n } -> {v:List Int | n < mylen v} -> Int @-}
get :: Int -> List Int -> Int
get n (Cons x xs) = if n == 0 then x else get (n-1) xs
get _ _           = error "index out of bounds"

{-@ test :: () -> {v:() | get 0 Nil == 0 } @-}
test :: () -> ()
test _ = undefined
