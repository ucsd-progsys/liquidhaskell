module spec Data.Vector where

import GHC.Base
import Data.Foldable


measure vlen    :: forall a. (Data.Vector.Vector a) -> Int

invariant       {v: Data.Vector.Vector a | 0 <= vlen v } 

assume !         :: forall a. x:(Data.Vector.Vector a) -> vec:{v:Nat | v < vlen x } -> a 

assume fromList  :: forall a. x:[a] -> {v: Data.Vector.Vector a  | vlen v = length x }

assume Data.Vector.length    :: x:Data.Vector.Vector a -> {v : Nat | v = vlen x }

assume replicate :: n:Nat -> a -> {v:Data.Vector.Vector a | vlen v = n} 
