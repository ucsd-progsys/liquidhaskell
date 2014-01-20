% Function Composition

Function Composition
--------------------

\begin{code}
module Composition where
\end{code}

A Plus Function
---------------

Consider a simple `plus` function 

\begin{code}
{-@ plus :: x:Int -> y:Int -> {v:Int | v = x + y} @-}
plus     :: Int -> Int -> Int
plus x y = x + y
\end{code}

A Simple Addition 
-----------------

Consider a simple use of `plus` a function that adds `3` to its input:

\begin{code}
{-@ plus3' :: x:Int -> {v:Int | v = x + 3} @-}
plus3'     :: Int -> Int
plus3' x   = x + 3
\end{code}

- The refinement type captures its behaviour...

- ... and LiquidHaskell easily verifies this type.

A Composed Variant
------------------

Instead, suppose we defined the previous function by composition 

We first add `2` to the argument and then add `1` to the intermediate result...

\begin{code}
{-@ plus3'' :: x:Int -> {v:Int | v = x + 3} @-}
plus3''     :: Int -> Int
plus3''     = (plus 1) . (plus 2)
\end{code}

but verification **fails** as we need a way to **compose** the refinements!

**Problem** What is a suitable description of the compose operator

\begin{code} _ 
(.) :: (b -> c) -> (a -> b) -> (a -> c)
\end{code}

that lets us **relate** `a` and `c` via `b` ?



Composing Refinements, Abstractly
---------------------------------

- We can analyze the *composition* operator

- With a very *descriptive* abstract refinement type!

\begin{code}

{-@ cc :: forall < p :: b -> c -> Prop
                , q :: a -> b -> Prop>.
         f:(x:b -> c<p x>) 
      -> g:(x:a -> b<q x>) 
      -> y:a 
      -> exists[z:b<q y>].c<p z>
 @-}

cc :: (b -> c) -> (a -> b) -> a -> c
cc f g x = f (g x)
\end{code}

Using Composition
-----------------

We can verify the desired `plus3` function:

\begin{code}
{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     :: Int -> Int
plus3     = (+ 1) `cc` (+ 2)
\end{code}

LiquidHaskell verifies the above, by **instantiating**

- `p` with `v = x + 1`
- `q` with `v = x + 2`

which lets it infer that the output of `plus3` has type:

- `exists [z:{v=y+2}]. {v = z + 1}`

which is a subtype of `{v:Int | v = 3}`

