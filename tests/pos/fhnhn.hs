module Fhnhn (main) where

-- In order to automatically infer invariants like this inside higher-order functions, it would be helpful for us to take *unannotated* functions and to them add implicit arguments for each HOf like tachio does.

{-@ f :: a:Int ~> ( () -> {v:_|v=a} ) -> (() -> {v:_|v=a}) -> () @-}
f :: (() -> Int) -> ( () -> Int) -> ()
f x y = assert (x () == y ())

h x () = x

main n = f (h n) (h n)

------------------------------------------------------
{-@ assume liquidAssert :: {v:Bool | v} -> a -> a  @-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

assert x = liquidAssert x ()
