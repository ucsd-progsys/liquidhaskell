module T1278_3 where

data List a = Nil | Cons a (List a)

-- First argument constant
mymap :: (a -> b) -> List a -> List b
mymap f Nil = Nil
mymap f (Cons x xs) = Cons (f x) (mymap f xs)

-- Lexicographic
ack :: List () -> List () -> List ()
ack Nil n = Cons () n
ack (Cons () m) Nil = ack m (Cons () Nil)
ack m'@(Cons () m) (Cons () n) = ack m (ack m' n)
