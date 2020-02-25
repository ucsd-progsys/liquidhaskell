module spec GHC.Base where

import GHC.CString
import GHC.Prim
import GHC.Classes
import GHC.Types

embed GHC.Types.Int      as int
embed GHC.Types.Bool     as bool

measure autolen :: forall a. a -> GHC.Types.Int

//class measure len :: forall f a. f a -> GHC.Types.Int
instance measure len :: forall a. [a] -> GHC.Types.Int
len []     = 0
len (y:ys) = 1 + len ys

// measure null :: [a] -> Bool
// null []     = true 
// null (y:ys) = false

//measure fst :: (a, b) -> a
//fst (a, b) = a
//
//measure snd :: (a, b) -> b
//snd (a, b) = b
//
//qualif Fst(__v:a, __y:b): (__v = (fst __y))
//qualif Snd(__v:a, __y:b): (__v = (snd __y))

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

// data variance Text.ParserCombinators.ReadPrec.ReadPrec contravariant

//qualif NonNull(v: [a])        : (? (nonnull v ))
//qualif Null(v: [a])           : (~ (? (nonnull v )))
//qualif EqNull(v:Bool, ~A: [a]): (v <=> (? (nonnull([~A]))))

// qualif IsEmp(v:GHC.Types.Bool, ~A: [a]) : ((v) <=> len([~A]) [ > ;  = ] 0)
// qualif ListZ(v: [a])          : len v  [ = ; >= ; > ] 0 
// qualif CmpLen(v:[a], ~A:[b])  : len v  [= ; >=; >; <=; <] len([~A]) 
// qualif EqLen(v:int, ~A: [a])  : v = len([~A]) 
// qualif LenEq(v:[a], ~A: int)  : ~A = len v  
// qualif LenAcc(v:int, ~A:[a], ~B: int): v = len([~A]) + ~B
// qualif LenDiff(v:[a], ~A:int): len v  = (~A [ +; - ] 1)

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


