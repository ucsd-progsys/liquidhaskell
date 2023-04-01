module spec GHC.Base where

import GHC.CString
import GHC.Classes
import GHC.Types

GHC.Base.. :: forall <p :: b -> c -> Bool, q :: a -> b -> Bool, r :: a -> c -> Bool>. 
                   {xcmp::a, wcmp::b<q xcmp> |- c<p wcmp> <: c<r xcmp>}
                   (ycmp:b -> c<p ycmp>)
                -> (zcmp:a -> b<q zcmp>)
                ->  xcmp:a -> c<r xcmp>

measure autolen :: forall a. a -> GHC.Types.Int

instance measure len :: forall a. [a] -> GHC.Types.Int
  len []     = 0
  len (y:ys) = 1 + len ys

measure fst :: (a, b) -> a
  fst (a, b) = a

measure snd :: (a, b) -> b
  snd (a, b) = b

qualif Fst(__v:a, __y:b): (__v = (fst __y))
qualif Snd(__v:a, __y:b): (__v = (snd __y))

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
