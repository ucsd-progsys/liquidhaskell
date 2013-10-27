module spec Data.Vector where

import GHC.Base

measure vlen    :: forall a. (Data.Vector.Vector a) -> Int

invariant       {v: Data.Vector.Vector a | (vlen v) >= 0 } 

assume !        :: forall a. x:(Data.Vector.Vector a) -> vec:{v: Int | ((0 <= v) && (v < (vlen x))) } -> a 

assume fromList :: forall a. x:[a] -> {v: Data.Vector.Vector a  | (vlen v) = (len x) }

assume length   :: forall a. x:(Data.Vector.Vector a) -> {v: Int | (v = (vlen x) && v >= 0) }
