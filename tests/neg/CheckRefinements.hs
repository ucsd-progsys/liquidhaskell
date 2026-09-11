{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{- LIQUID "--check-refinements" @-}

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
mylen :: List a -> Int
mylen Nil = 0
mylen (Cons _ xs) = 1 + mylen xs

{-@ reflect get @-}
get :: Int -> List Int -> Int
get _ Nil = error "index out of bounds"
get 0 (Cons x _) = x
get n (Cons _ xs) = get (n-1) xs
{-@ get :: n:{Int | n >= 0} -> {v:List Int | mylen v > n} -> Int @-}

{-@ test :: () -> {v:() | get 0 Nil == 0 } @-}
test :: () -> ()
test _ = undefined
