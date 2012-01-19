module Range where

import Control.Applicative
import LiquidPrelude

data LL a = N | C a (LL a)

--instance Functor LL where
--  fmap f N                = N
--  fmap f (C jhala jhalas) = C (f jhala) (fmap f jhalas)

incr x = x `plus` 1

lmap f N = N
lmap f (C jhala jhalas) = C (f jhala) (lmap f jhalas)

range :: Int -> Int -> LL Int
range i j = C i N

n = choose 0

prop_rng1 = (assert . (0 `leq`)) `lmap` range 0 n


poo = C 1 
