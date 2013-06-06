module Mod1 where

data Goo = G Int

{-@ measure myg :: Mod1.Goo -> Int 
    myg (Mod1.G n) = n
  @-}
 
{-@ inc :: x:Mod1.Goo -> {v: Mod1.Goo | (myg v) > (myg x)} @-}
inc (G x) = G (x + 1)

