module spec Prelude where

import GHC.Base

assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}

assume True     :: {v : Bool | (? v)}
assume False    :: {v : Bool | (~ (? v))}

assume (&&)     :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
assume (==)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume (/=)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume (>)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume (>=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume (<)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume (<=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
assume ($)      :: (x:a -> b) -> a -> b

assume compare  :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}
assume id       :: x:a -> {v:a | v = x}

-- TODO: assume ($)      :: forall <p :: a -> Bool>. (x: a -> b<p x>) -> y:a -> b<p y>


assume (+)         :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume (-)         :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume (*)         :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume div         :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume fromInteger :: (Num a) => x:Integer -> {v:a | v = x }

