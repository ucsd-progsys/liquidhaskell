module GhcSort where

import Language.Haskell.Liquid.Prelude
-- This is SAFE
{-@ bar :: (Ord a) => a -> a -> {v: Bool | (? v)} @-}
bar a b
  = case a `compare` b of
    GT        -> True
    otherwise -> liquidAssertB (a <= b)

-- This is UNSAFE:
{-@ foo :: (Ord a) => a -> a -> {v: Bool | (? v)} @-}
foo a b 
  | a `compare` b == GT = True
  | otherwise           = liquidAssertB (a <= b)




