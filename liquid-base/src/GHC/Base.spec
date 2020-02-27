module spec GHC.Base where

import GHC.CString
import GHC.Prim
import GHC.Classes
import GHC.Types

GHC.Types.W# :: w:_ -> {v:GHC.Types.Word | v == w }

assume GHC.Types.D# :: x:GHC.Prim.Double# -> {v: GHC.Types.Double | v = (x :: real) }
assume GHC.Types.F# :: x:GHC.Prim.Float# -> {v: GHC.Types.Float | v = (x :: real) }
assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
assume GHC.Types.C# :: x:GHC.Prim.Char# -> {v: GHC.Types.Char | v = (x :: Char) }

measure autolen :: forall a. a -> GHC.Types.Int

instance measure len :: forall a. [a] -> GHC.Types.Int
len []     = 0
len (y:ys) = 1 + len ys

measure isJust :: Maybe a -> Bool
isJust (Just x)  = true
isJust (Nothing) = false

measure fromJust :: Maybe a -> a
fromJust (Just x) = x

invariant {v: [a] | len v >= 0 }
map       :: (a -> b) -> xs:[a] -> {v: [b] | len v == len xs}
(++)      :: xs:[a] -> ys:[a] -> {v:[a] | len v == len xs + len ys}

($)       :: (a -> b) -> a -> b
id        :: x:a -> {v:a | v = x}

qualif IsEmp(v:GHC.Types.Bool, xs: [a]) : (v <=> (len xs > 0))
qualif IsEmp(v:GHC.Types.Bool, xs: [a]) : (v <=> (len xs = 0))

qualif ListZ(v: [a])          : (len v =  0) 
qualif ListZ(v: [a])          : (len v >= 0) 
qualif ListZ(v: [a])          : (len v >  0) 

qualif CmpLen(v:[a], xs:[b])  : (len v  =  len xs ) 
qualif CmpLen(v:[a], xs:[b])  : (len v  >= len xs ) 
qualif CmpLen(v:[a], xs:[b])  : (len v  >  len xs ) 
qualif CmpLen(v:[a], xs:[b])  : (len v  <= len xs ) 
qualif CmpLen(v:[a], xs:[b])  : (len v  <  len xs ) 

qualif EqLen(v:int, xs: [a])  : (v = len xs ) 
qualif LenEq(v:[a], x: int)   : (x = len v ) 

qualif LenDiff(v:[a], x:int)  : (len v  = x + 1)
qualif LenDiff(v:[a], x:int)  : (len v  = x - 1)
qualif LenAcc(v:int, xs:[a], n: int): (v = len xs  + n)
