module Mod1 where

data Goo = G Int

{-@ measure myg :: Mod1.Goo -> Int 
    myg (Mod1.G n) = n
  @-}
 
{-@ inc :: x:Goo -> {v: Goo | (myg v) > (myg x)} @-}
inc (G x) = G (x + 1)


