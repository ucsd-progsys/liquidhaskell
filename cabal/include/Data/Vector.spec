module spec Data.Vector where

import Data.List

measure vlen                :: forall a. (Vector a) -> Int 
assume (!)                  :: forall a. x:(Vector a) -> {v: Int | ((0 <= v) && (v < vlen(x))) } -> a 

assume Data.Vector.fromList :: forall a. x:[a] -> { v: Vector a | vlen(v) = len(x) }
assume Data.Vector.length   :: forall a. x:(Vector a) -> {v : Int | v = vlen(x)}

