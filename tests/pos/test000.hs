module Test0 () where

import Language.Haskell.Liquid.Prelude

toss :: Bool 
toss = (choose 0) > 10

prop_abs :: Bool
prop_abs = if toss 
             then (if toss then liquidAssertB toss else False) 
             else False

foo :: Int -> Int
foo x = (liquidAssert (x > 0) x) + 1

goo = foo 12

incr :: Int -> Int
incr zzz = zzz + 1

zoo = incr 29


