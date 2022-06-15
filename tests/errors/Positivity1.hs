{-@ LIQUID "--expect-error-containing=Negative occurence of Positivity1.Rec" @-}
module Positivity1 where

newtype Rec a = In { out :: Rec a -> a }

y :: (a -> a) -> a
y f = g (In g)
  where
    -- ghc would say: Simplifier ticks exhausted
    -- if we don't prevent this from inlining
    {-# NOINLINE g #-}
    g x = f (out x x)

{-@ foo :: n:Nat -> {v:Nat | v < n} @-}
foo :: Int -> Int
foo = y go
  where go f n = if n > 0 then n-1 else f n

prop = let x = 0 in
       assert ((\n -> 0==1) (foo 0))

{-@ assert :: b:{Bool | b} -> () @-} 
assert :: Bool -> () 
assert _ = () 
