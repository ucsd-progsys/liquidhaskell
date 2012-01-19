module spec Prelude where

import Data.List

assume True   :: {v : Bool | (? v)}
assume False  :: {v : Bool | (~ (? v))}
assume (&&)   :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}

assume div   :: forall a. (Num a) => x:a -> y:a -> {v:a | v = (x / y) }
assume (*)   :: forall a. (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume (+)   :: forall a. (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume (-)   :: forall a. (Num a) => x:a -> y:a -> {v:a | v = x - y }

assume (==)  :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume (/=)  :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume (>)   :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume (>=)  :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume (<)   :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume (<=)  :: forall a. (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}

assume GHC.Types.I#             :: x : GHC.Prim.Int# -> {v: Int | v = (x :: Int) }   
assume GHC.Num.fromInteger      :: forall a. (Num a) => x:Integer -> {v:a | v = x }
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}

assume id      :: forall a. x:a -> {v:a | v = x}

assume map     :: forall a, b. f:(a -> b) -> xs:[a] -> {v:[b] | len(v) = len(xs)}

assume zipWith :: forall a, b, c. f:(p:a -> q:b -> c) 
                               -> xs : [a] 
                               -> ys:{v:[b] | len(v) = len(xs)} 
                               -> {v : [c] | len(v) = len(xs)} 

