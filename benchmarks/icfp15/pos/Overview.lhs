\begin{code}
module OverView where 
{-@ LIQUID "--no-termination" @-}
\end{code}


2.2 Bounded Refinements
-----------------------

\begin{code}
{-@ bound UpClosed (p :: Int -> Prop) 
  = \(x :: Int) (v :: Int)  
  -> p x => v = x + 1 => p v @-}


{-@ find :: forall <p :: Int -> Prop>.
            (UpClosed p) => 
            (Int -> Bool) -> (Int<p> -> a) -> Int<p> -> a @-}

find :: (Int -> Bool) -> (Int -> a) -> Int -> a
find q k i | q i       = k i
           | otherwise = find q k (i + 1)
\end{code}


2.3 Bounds for Higher-Order Functions
-------------------------------------

\begin{code}

{-@ bound Chain (p :: b -> c -> Prop) (q :: a -> b -> Prop) (r :: a -> c -> Prop) = 
    \(x :: a) (y :: b) (z :: c) -> true => q x y =>  p y z => r x z 
  @-}

-- {x::a, w::b<q x> |- c<p w> <: c<r x>}

{-@ 
(.) :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
       (Chain p q r) => 
       (y:b -> c<p y>)
    -> (z:a -> b<q z>)
    ->  x:a -> c<r x>
@-}    
(.) f g x = f (g x)   

{-@ plusminus :: n:Nat -> m:Nat -> x:{Nat | x <= m} -> {v:Nat | v = (m - x) + n} @-}
plusminus :: Int -> Int -> Int -> Int
plusminus n m = (n+) . (m-)

{-@ qualif PLUSMINUS(v:int, x:int, y:int, z:int): (v = (x - y) + z) @-}
{-@ qualif PLUS     (v:int, x:int, y:int)       : (v = x + y)       @-}
{-@ qualif MINUS    (v:int, x:int, y:int)       : (v = x - y)       @-}
\end{code}