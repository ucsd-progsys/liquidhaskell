module Range where

import Language.Haskell.Liquid.Prelude

data Foo a = F a a a 

data LL a = N | C a (LL a)

{-@ data LL [llen] a = N | C (x::a) (xs::(LL a)) @-}

{-@ invariant {v:LL a | (llen v) >= 0} @-}

{-@ measure llen :: (LL a) -> Int 
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

lmap f N = N
lmap f (C x xs) = C (f x) (lmap f xs)

range :: Int -> Int -> LL Int
range i j = C i N

n = choose 0

prop_rng1 = (liquidAssertB . (0 <=)) `lmap` range 0 n

--poo :: LL Int
poo = C (1 :: Int) 
