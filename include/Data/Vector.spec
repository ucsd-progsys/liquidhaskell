module spec Data.Vector where

import GHC.Base

data variance Data.Vector.Vector covariant


measure vlen    :: forall a. (Data.Vector.Vector a) -> Int

invariant       {v: Data.Vector.Vector a | 0 <= vlen v } 

!           :: forall a. x:(Data.Vector.Vector a) -> vec:{v:Nat | v < vlen x } -> a 

unsafeIndex :: forall a. x:(Data.Vector.Vector a) -> vec:{v:Nat | v < vlen x } -> a 

fromList  :: forall a. x:[a] -> {v: Data.Vector.Vector a  | vlen v = len x }

length    :: forall a. x:(Data.Vector.Vector a) -> {v : Nat | v = vlen x }

replicate :: n:Nat -> a -> {v:Data.Vector.Vector a | vlen v = n} 

imap :: (Nat -> a -> b) -> x:(Data.Vector.Vector a) -> {y:Data.Vector.Vector b | vlen y = vlen x }

map :: (a -> b) -> x:(Data.Vector.Vector a) -> {y:Data.Vector.Vector b | vlen y = vlen x }
