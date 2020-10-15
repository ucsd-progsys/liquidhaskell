module ModLib where

data Goo = G Int

{-@ measure myg :: ModLib.Goo -> Int 
      myg (ModLib.G n) = n
  @-}
 
{-@ inc :: x:Goo -> {v: Goo | (myg v) > (myg x)} @-}
inc (G x) = G (x + 1)


