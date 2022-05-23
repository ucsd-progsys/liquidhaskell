module Data2 (prop_rng1, llen) where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

data LL a = N | C { headC :: a, tailC :: (LL a) }
{-@ data LL [llen] a = N | C { headC :: a, tailC :: (LL a) } @-}

{-@ measure llen @-}
llen :: LL a -> Int 
{-@ llen :: LL a -> Nat @-}
llen N = 0 
llen (C _ xs) = 1 + llen xs 

--instance Functor LL where
--  fmap f N                = N
--  fmap f (C jhala jhalas) = C (f jhala) (fmap f jhalas)

lmap f N = N
lmap f (C jhala jhalas) = C (f jhala) (lmap f jhalas)

range :: Int -> Int -> LL Int
range i j = C i N

prop_rng1 n   = (liquidAssertB . (0 <=)) `lmap` range 0 n
