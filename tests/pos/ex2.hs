module Blank where

-- Currently, we cannot write the signature:

{- :: x : Int -> g : (z: Int -> Int) -> {v : Int | v = (g x) + 1} -}

-- as it uses a "raw" haskell level function `g` in the output refinement.
-- But instead, we can use abstract refinements [see the ESOP 2013 paper]
-- to write the signature:

{-@ f :: forall <p :: Int -> Int -> Prop>. 
           x:Int -> (z:Int -> Int<p z>) -> exists[z:Int<p x>]. {v:Int | v = z + 1} 
  @-}
f :: Int -> (Int -> Int) -> Int
f x g = (g x) + 1

-- And now we can verify uses of `f` as expected at various call-sites.

foo, bar :: Int -> Int

{-@ foo :: x:Int -> {v:Int | v = x + 1} @-}
foo x = x + 1

{-@ bar :: x:Int -> {v:Int | v = x - 1} @-}
bar x = x - 1

{-@ plusTwo :: x:Int -> {v:Int | v = x + 2} @-}
plusTwo x = f x foo

{-@ plusZero :: x:Int -> {v:Int | v = x} @-}
plusZero x = f x bar

