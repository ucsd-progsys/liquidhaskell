module spec Data.Vector where

import GHC.Base

measure vlen    :: forall a. (Vector a) -> Int

invariant       {v: Vector a | (vlen v) >= 0 } 

assume !        :: forall a. x:(Vector a) -> vec:{v: Int | ((0 <= v) && (v < (vlen x))) } -> a 

assume fromList :: forall a. x:[a] -> {v: Vector a  | (vlen v) = (len x) }

assume length   :: forall a. x:(Vector a) -> {v: Int | (v = (vlen x) && v >= 0) }
