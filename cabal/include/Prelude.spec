module spec Prelude where

import GHC.Base

assume div   :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume (*)   :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume (+)   :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume (-)   :: (Num a) => x:a -> y:a -> {v:a | v = x - y }

assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}


assume Prelude.replicate        :: n: Int -> a -> {v: [a] | len(v) = n }
assume Prelude.take             :: n: Int -> [a] -> {v: [a] | len(v) = n }
assume Prelude.length           :: x: [a] -> { v: Int | v = len(x) }
assume Prelude.map              :: (a -> b) -> xs:[a] -> {v: [b] | v = len(xs)}
assume Prelude.tail             :: xs:[a] -> {v:[a] | len(v) = len(xs) - 1}
assume Prelude.zipWith          :: f:(p:a -> q:b -> c) 
                                   -> xs : [a] 
                                   -> ys:{v:[b] | len(v) = len(xs)} 
                                   -> {v : [c] | len(v) = len(xs)} 
