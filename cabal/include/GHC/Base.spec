module spec GHC.Base where

import GHC.Prim

measure len :: forall a. [a] -> Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)

invariant          {v: [a] | len(v) >= 0 }

assume True     :: {v : Bool | (? v)}
assume False    :: {v : Bool | (~ (? v))}

--assume (&&)     :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
--assume (==)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
--assume (/=)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
--assume (>)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
--assume (>=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
--assume (<)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
--assume (<=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
--assume ($)      :: (x:a -> b) -> a -> b

assume compare  :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}
assume id       :: x:a -> {v:a | v = x}

-- TODO: assume ($)      :: forall <p :: a -> Bool>. (x: a -> b<p x>) -> y:a -> b<p y>

