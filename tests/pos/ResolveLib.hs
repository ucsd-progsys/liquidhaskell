module ResolveLib where

import qualified ResolveLibLib as RB
import qualified ResolveLibLib

{-@ measure getFooA :: Foo -> Int
      getFooA (Foo x) = x
  @-}

data Foo = Foo Int

y = RB.Foo 1
z = RB.A 
{-@ qualif NotA(v:RB.Bar): (notA v) @-}

{-@ measure notA :: RB.Bar -> Bool
      notA RB.A = false
      notA RB.B = true
      notA RB.C = false
  @-}

{-@ predicate NotA V = V != RB.A @-}
