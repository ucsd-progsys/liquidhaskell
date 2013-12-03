module Blank where

-- This example is unsound due to non-recursive definition of llen 

import Language.Haskell.Liquid.Prelude

data L a = N | C a (L a)


{-@ measure llen :: (L a) -> Int 
    llen(N) = 0
    llen(C x xs) = 1 + (llen (C x xs))
  @-}
  
foo :: L a -> L a
foo (C _ xs) = liquidAssert (0==1) xs
