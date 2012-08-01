module spec Prelude where

import GHC.Base

assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:Integer | v = (x :: Integer)}
assume GHC.Types.True     :: {v : Bool | (? v)}
assume GHC.Types.False    :: {v : Bool | (~ (? v))}
assume GHC.Classes.&&     :: x: Bool -> y: Bool -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
assume GHC.Classes.==     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume GHC.Classes./=     :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume GHC.Classes.>      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume GHC.Classes.>=     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume GHC.Classes.<      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume GHC.Classes.<=     :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
assume GHC.Base.$         :: (x:a -> b) -> a -> b

assume GHC.Classes.compare  :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}
assume GHC.Base.id :: x:a -> {v:a | v = x}

-- TODO: assume ($)      :: forall <p :: a -> Bool>. (x: a -> b<p x>) -> y:a -> b<p y>

assume GHC.Num.+           :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-           :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*           :: (Num a) => x:a -> y:a -> {v:a | (((x >= 0) && (y >= 0)) => (v >= 0)) }
assume div                 :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
assume GHC.Num.fromInteger :: (Num a) => x:Integer -> {v:a | v = x }
