\begin{code}
module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)
\end{code}

Indexed-Dependent Refinements
=============================

We illustrate how to use abstract refinements to talk about 
indexed-dependent invariants.

We use a Vector of `a`s implemented as a function from `Int` to `a`s

\begin{code}
data Vec a = V (Int -> a)
\end{code}

We abstract over the `dom` that describes the domain
and `rng` that describes the value with respect to its index.

\begin{code}
{-@
data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
     = V {a :: i:Int<dom> -> a <rng i>}
  @-}
\end{code}

With this we can describe interesting vectors:

A vector of `Int` defined on values less than `100`
containing values equal to their index:
\begin{code}
{-@ type IdVec = 
     Vec <{\v -> (v < 100)}, {\j v -> (v = j)}> Int
  @-}
\end{code}

A vector defined on the range `[0..n)` with its last element equal to `0`:
\begin{code}
{-@ type ZeroTerm N = 
     Vec <{\v -> (0 <= v && v < N)}, {\j v -> (j = N - 1 => v = 0)}> Int
  @-}
\end{code}

Or a vector defined on integers whose value at index `i` is either 
`0` or the `i`th fibonacci:
\begin{code}
{-@ measure fib :: Int -> Int @-}
{-@ type FibV = 
     Vec <{\v -> 0=0}, {\j v -> ((v != 0) => (v = fib(j)))}> Int @-}
\end{code}


Operations on Vectors
---------------------

As a next step we give appropriate types to vector operations:


`empty` returns a Vector whose domain is always false:
\begin{code}
{-@ empty :: forall <p :: Int -> a -> Prop>. Vec <{\v -> 0=1}, p> a @-}
empty     :: Vec  a
empty     = V $ \_ -> (error "Empty array!")
\end{code}

If we `get` the `i`th element of an array, 
the result should satisfy the range at `i`:
\begin{code} 
{-@ get :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
             i: Int<d> ->
             a: Vec<d, r> a ->
             a<r i> @-}
get :: Int -> Vec a -> a
get i (V f) = f i
\end{code}

Finally, if we `set` the `i`th element of a Vector to a value
that satisfies range at `i`, 
then Vector's domain will be extended with `i`:
\begin{code}
{-@ set :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
      i: Int<d> ->
      x: a<r i> ->
      a: Vec <{v:Int<d> | v != i}, r> a -> 
      Vec <d, r> a @-}
set :: Int -> a -> Vec a -> Vec a
set i v (V f) = V $ \k -> if k == i then v else f k
\end{code}

Using Vectors
-------------

In the following example, we use the previous Vector operations
to efficiently compute the `i`th fibonacci number:

\begin{code}
{-@ assume axiom_fib :: i:Int -> {v: Bool | (Prop(v) <=> (fib(i) = ((i <= 1) ? 1 : ((fib(i-1)) + (fib(i-2)))))) } @-}
axiom_fib :: Int -> Bool
axiom_fib i = undefined

{-@ fastFib :: x:Int -> {v:Int | v = fib(x)} @-}
fastFib     :: Int -> Int
fastFib n   = snd $ fibMemo (V (\_ -> 0)) n


{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = fib(i)}) @-}
fibMemo :: Vec Int -> Int -> (Vec Int, Int)
fibMemo t i 
  | i <= 1    
  = (t, liquidAssume (axiom_fib i) (1 :: Int))
  
  | otherwise 
  = case get i t of   
      0 -> let (t1, n1) = fibMemo t  (i-1)
               (t2, n2) = fibMemo t1 (i-2)
               n        = liquidAssume (axiom_fib i) (n1 + n2)
           in  (set i n t2,  n)
      n -> (t, n)
\end{code}
