module Range (prop_rng1) where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

data LL a = N | C { head :: a, tail :: (LL a) }
{-@ data LL [llen] a = N | C { head :: a, tail :: (LL a) } @-}

{-@ measure llen :: (LL a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs) 
  @-}

{-@ invariant {v:LL a | (llen v) >= 0} @-}

--instance Functor LL where
--  fmap f N                = N
--  fmap f (C jhala jhalas) = C (f jhala) (fmap f jhalas)

lmap f N = N
lmap f (C jhala jhalas) = C (f jhala) (lmap f jhalas)

range :: Int -> Int -> LL Int
range i j = C i N

prop_rng1 n   = (liquidAssertB . (0 <=)) `lmap` range 0 n
