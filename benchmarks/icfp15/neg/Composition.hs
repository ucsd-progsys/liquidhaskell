module Compose where

{-@ 
cmp :: forall < p :: b -> c -> Prop
              , q :: a -> b -> Prop
              , r :: a -> c -> Prop
              >. 
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       f:(y:b -> c<p y>)
    -> g:(z:a -> b<q z>)
    -> x:a -> c<r x>
@-}

cmp :: (b -> c)
    -> (a -> b)
    ->  a -> c

cmp f g x = f (g x)    



{-@ incr :: x:Nat -> {v:Nat | v == x + 1} @-}
incr :: Int -> Int
incr x = x + 1


{-@ incr2 :: x:Nat -> {v:Nat | v = x + 2} @-}
incr2 :: Int -> Int
incr2 = incr `cmp` incr

{-@ incr2' :: x:Nat -> {v:Nat | v = x + 2} @-}
incr2' :: Int -> Int
incr2' = incr `cmp` incr

{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v < (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) `cmp` (m-)


{-@ plus :: n:a -> x:a -> {v:a | v = (x + n)} @-}
plus :: Num a => a -> a -> a
plus = undefined 
minus :: Num a => a -> a -> a
{-@ minus :: n:a -> x:a -> {v:a | v = x - n} @-}
minus _ _ = undefined

{-@ plus1 :: x:Nat -> {v:Nat | v == x + 20} @-}
plus1 :: Int -> Int
plus1 x = x + 20

{-@ plus2 :: x:{v:Nat | v > 10} -> {v:Nat | v == x + 2} @-}
plus2 :: Int -> Int
plus2 x = x + 2

{-@ plus42 :: x:Nat -> {v:Nat | v == x + 42} @-}
plus42 :: Int -> Int
plus42 = cmp plus2 plus1



{-@ qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{-@ qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{-@ qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}





