module spec Prelude where

import GHC.Base

assume True   :: {v : Bool | (? v)}
assume False  :: {v : Bool | (~ (? v))}
assume (&&)   :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}

assume div   :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume (*)   :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume (+)   :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume (-)   :: (Num a) => x:a -> y:a -> {v:a | v = x - y }

assume (==)  :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume (/=)  :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume (>)   :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume (>=)  :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume (<)   :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume (<=)  :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}

assume compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}


assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}

assume id                       :: x:a -> {v:a | v = x}
assume ($)                      :: (x:a -> b) -> a -> b

assume Prelude.length           :: x: [a] -> { v: Int | v = len(x) }
assume Prelude.map              :: (a -> b) -> [a] -> [b]
assume Prelude.tail             :: xs:[a] -> {v:[a] | len(v) = len(xs) - 1}
assume Prelude.zipWith          :: f:(p:a -> q:b -> c) 
                                   -> xs : [a] 
                                   -> ys:{v:[b] | len(v) = len(xs)} 
                                   -> {v : [c] | len(v) = len(xs)} 
