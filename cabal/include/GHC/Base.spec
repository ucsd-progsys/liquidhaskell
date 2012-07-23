module spec GHC.Base where

import GHC.Prim

measure len :: forall a. [a] -> Int
len ([])     = 0
len (y:ys)   = 1 + len(ys)

measure nully :: forall a. [a] -> Int
nully (y:ys) = 1
nully ([])   = 0

measure nonnull :: forall a. [a] -> Bool 
nonnull (y:ys) = true
nonnull ([])   = false 

-- assume error :: {v: String | 0 = 1} -> a

invariant {v: [a] | len(v) >= 0 }

assume True     :: {v : Bool | (? v)}
assume False    :: {v : Bool | (~ (? v))}
assume (&&)     :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
assume (==)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume (/=)     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume (>)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume (>=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume (<)      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume (<=)     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
assume compare  :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}
assume id       :: x:a -> {v:a | v = x}
assume ($)      :: (x:a -> b) -> a -> b
