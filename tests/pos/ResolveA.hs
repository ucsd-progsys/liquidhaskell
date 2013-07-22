module ResolveA where

import qualified ResolveB as RB

{-@ measure getFooA :: RB.Foo -> Int
    getFooA (RB.Foo x) = x
  @-}


y = RB.Foo 1
