\begin{code}
module ICFP15 where

import Prelude hiding ((.))

import Language.Haskell.Liquid.Prelude (liquidAssert, liquidAssume)
\end{code}

Function Composition: Bringing Everything into Scope!
-----------------------------------------------------

- Definition

\begin{code}
{-@ 
(.) :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
       {x::a, w::b<q x> |- c<p w> <: c<r x>}
       (y:b -> c<p y>)
    -> (z:a -> b<q z>)
    ->  x:a -> c<r x>
@-}    
(.) f g x = f (g x)    
\end{code}

- Usage 

\begin{code}
{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)
\end{code}

- Qualifiers

\begin{code}
{-@ qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{-@ qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{-@ qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}
\end{code}