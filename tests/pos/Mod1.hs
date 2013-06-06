module Mod1 where



data Goo = G Int

{-@ data Goo = G (x :: {v: Int | 0 > true}) @-}

{-@ measure myg :: Mod1.Goo -> Int 
    myg (Mod1.G n) = n
  @-}
 
{-@ inc :: x:Goo -> {v: Goo | (myg v) > (myg x)} @-}
inc (G x) = G (x + 1)


{-@ moo :: {v: Int | 0 > true } @-}
moo :: Int
moo = 0
