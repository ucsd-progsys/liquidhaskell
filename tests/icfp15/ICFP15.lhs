\begin{code}
module ICFP15 where

import Prelude hiding ((.))
\end{code}

Function Composition: Bringing Everything into Scope!
-----------------------------------------------------

- Definition

\begin{code}
{-@ 
(.) :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       f:(y:b -> c<p y>)
    -> g:(z:a -> b<q z>)
    ->   x:a -> c<r x>
@-}    
(.) f g x = f (g x)    
\end{code}

- Usage 

incr :: Int -> Int
{-@ incr :: x:Nat -> {v:Nat | v == x + 1} @-}
incr x = x + 1

incr2 :: Int -> Int
{-@ incr2 :: x:Nat -> {v:Nat | v == x + 2} @-}
incr2  = incr . incr 

plus :: Int -> Int -> Int
{-@ plus :: x:Nat -> y:Nat -> {v:Nat | v == x + y} @-}
plus x y = x + y

minus :: Int -> Int -> Int
{-@ minus :: x:Nat -> y:{Nat | y <= x} -> {v:Nat | v == x - y} @-}
minus x y = x - y


{-@ q :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | x = n + (m - v)} @-}
q = undefined
{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = n + (m - x)} @-}
q, plusminus :: Int -> Int -> Int -> Int
plusminus n m  = plus n . minus m 


p = \w v -> v = n + w
q = \x v -> v = m - x


w :: 




