module Rec where

import Language.Haskell.Liquid.Prelude

newtype Rec a = In { out :: Rec a -> a }
 
y :: (a -> a) -> a
y = \f -> (\x -> f (out x x)) (In (\x -> f (out x x)))


{-@ foo :: n:Nat -> {v:Nat | v < n} @-}
foo :: Int -> Int
foo = y go
  where go f n =  if n > 0 then n-1 else f n


prop = let x = 0 in
       liquidAssert ((\n -> 0==1) (foo 0))
