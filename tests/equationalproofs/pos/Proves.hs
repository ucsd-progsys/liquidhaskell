module Proves where

type Proof = Bool

infixl 3 ==:, <=:, <:, ?

(<=:) :: Ord a => a -> a -> Proof -> a 
{-@ (<=:) :: x:a -> y:a -> {v:Proof | x <= y } -> {v:a | v == x } @-} 
(<=:) x y _ = x

(<:) :: Ord a => a -> a -> Proof -> a 
{-@ (<:) :: x:a -> y:a -> {v:Proof | x < y } -> {v:a | v == x } @-} 
(<:) x y _ = x


(==:) :: Eq a => a -> a -> Proof -> a 
{-@ (==:) :: (Eq a) => x:a -> y:a -> {v:Proof| x == y} -> {v:a | v == x } @-} 
(==:) x y _ = x 


(?) :: (Proof -> a) -> Proof -> a 
f ? y = f y 

proof :: a -> Bool 
proof _ = True 