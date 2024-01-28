{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Vector_LHAssumptions where

import Data.Vector
import GHC.Base

{-@

data variance Data.Vector.Vector covariant


measure vlen    :: forall a. (Data.Vector.Vector a) -> Int

invariant       {v: Data.Vector.Vector a | 0 <= vlen v }

assume Data.Vector.!           :: forall a. x:(Data.Vector.Vector a) -> vec:{v:Nat | v < vlen x } -> a

assume Data.Vector.unsafeIndex :: forall a. x:(Data.Vector.Vector a) -> vec:{v:Nat | v < vlen x } -> a

assume Data.Vector.fromList  :: forall a. x:[a] -> {v: Data.Vector.Vector a  | vlen v = len x }

assume Data.Vector.length    :: forall a. x:(Data.Vector.Vector a) -> {v : Nat | v = vlen x }

assume Data.Vector.replicate :: n:Nat -> a -> {v:Data.Vector.Vector a | vlen v = n}

assume Data.Vector.imap :: (Nat -> a -> b) -> x:(Data.Vector.Vector a) -> {y:Data.Vector.Vector b | vlen y = vlen x }

assume Data.Vector.map :: (a -> b) -> x:(Data.Vector.Vector a) -> {y:Data.Vector.Vector b | vlen y = vlen x }

assume Data.Vector.head :: forall a. {xs: Data.Vector.Vector a | vlen xs > 0} -> a

qualif VecEmpty(v: Data.Vector.Vector a)    : (vlen v)  =  0
qualif VecEmpty(v: Data.Vector.Vector a)    : (vlen v)  >  0
qualif VecEmpty(v: Data.Vector.Vector a)    : (vlen v)  >= 0

qualif Vlen(v:int, x: Data.Vector.Vector a) : (v  =  vlen x)
qualif Vlen(v:int, x: Data.Vector.Vector a) : (v <=  vlen x)
qualif Vlen(v:int, x: Data.Vector.Vector a) : (v  <  vlen x)

qualif CmpVlen(v:Data.Vector.Vector a, x:Data.Vector.Vector b) : (vlen v <  vlen x)
qualif CmpVlen(v:Data.Vector.Vector a, x:Data.Vector.Vector b) : (vlen v <= vlen x)
qualif CmpVlen(v:Data.Vector.Vector a, x:Data.Vector.Vector b) : (vlen v >  vlen x)
qualif CmpVlen(v:Data.Vector.Vector a, x:Data.Vector.Vector b) : (vlen v >= vlen x)
qualif CmpVlen(v:Data.Vector.Vector a, x:Data.Vector.Vector b) : (vlen v =  vlen x)

@-}
