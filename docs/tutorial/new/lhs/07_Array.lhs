%Indexed-Dependent Refinements

Indexed-Dependent Refinements
-----------------------------

\begin{code}
module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)

{-@ LIQUID "--no-termination" @-}
\end{code}

Indexed-Dependent Refinements
-----------------------------

We define a Vector of `a`s 
implemented as a function from `Int` to `a`s <br>
<br>

\begin{code}
data Vec a = V (Int -> a)
\end{code}

Abstract Over the Domain and Range
----------------------------------

We parameterize the definition with two abstract refinements:
<br>
<br>

\begin{code}
{-@ data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
      = V {a :: i:Int<dom> -> a <rng i>}
  @-}
\end{code}


- `dom`: describes the *domain* 

- `rng`: describes each value with respect to its index

Describing Vectors
------------------

\begin{code}By instantiating these two predicates, we describe Vector's *domain* and *range*
{-@ data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
      = V {a :: i:Int<dom> -> a <rng i>}
  @-}
\end{code}
<br>

A vector of `Int` *defined on* values less than `42`
*containing values* equal to their index:
<br>
<br>

\begin{code}
{-@ type IdVec = 
      Vec <{\v -> (v < 42)}, {\j v -> (v = j)}> Int
  @-}
\end{code}

Describing Vectors
------------------
\begin{code}By instantiating these two predicates, we describe Vector's *domain* and *range*
{-@ data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
      = V {a :: i:Int<dom> -> a <rng i>}
  @-}
\end{code}
<br>

A vector *defined on* the range `[0..n)` with its *last element* equal to `0`:
<br>
<br>

\begin{code}
{-@ type ZeroTerm N = 
     Vec <{\v -> (0 <= v && v < N)}, {\j v -> (j = N - 1 => v = 0)}> Int
  @-}
\end{code}

Describing Vectors
------------------
\begin{code}By instantiating these two predicates, we describe Vector's *domain* and *range*
{-@ data Vec a <dom :: Int -> Prop, rng :: Int -> a -> Prop>
      = V {a :: i:Int<dom> -> a <rng i>}
  @-}
\end{code}
<br>


A vector *defined on* integers whose *value at index `j`* is either 
`0` or the `j`th fibonacci:
<br>
<br>

\begin{code}
{-@ type FibV =  
     Vec <{\v -> 0=0}, {\j v -> ((v != 0) => (v = (fib j)))}> Int 
  @-}
\end{code}


Operations on Vectors
---------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target= "_blank">Demo:</a> 

We give appropriate types to vector operations (empty, set, get...)

- This means *abstracting* over the domain and range


Empty
-----

`empty` returns a Vector whose domain is always false
<br>
<br>

\begin{code}
{-@ empty :: forall <p :: Int -> a -> Prop>. Vec < {v:Int | 0=1}, p> a @-}

empty     :: Vec  a
empty     = V $ \_ -> (error "Empty array!")
\end{code}

Typing Get
----------

If `i` satisfies the domain then
if we `get` the `i`th element of an array, 
the result should satisfy the range at `i`
<br>
<br>

\begin{code}
{-@ get :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
           i: Int<d>
        -> a: Vec<d, r> a
        -> a<r i> @-}

get :: Int -> Vec a -> a
get i (V f) = f i
\end{code}

Typing Set
----------

If `i` satisfies the domain then
if we `set` the `i`th element of a Vector to a value
that satisfies range at `i`, 
then Vector's domain will be extended with `i`
<br>
<br>

\begin{code}
{-@ set :: forall a <r :: Int -> a -> Prop, d :: Int -> Prop>.
           i: Int<d>
        -> x: a<r i>
        -> a: Vec < {v:Int<d> | v != i}, r> a
        -> Vec <d, r> a @-}

set :: Int -> a -> Vec a -> Vec a
set i v (V f) = V $ \k -> if k == i then v else f k
\end{code}

Using Vectors
-------------

\begin{code}Remember the fibonacci memoization Vector:
type FibV = 
     Vec <{\v -> 0=0}, {\j v -> ((v != 0) => (v = (fib j)))}> Int
\end{code}
<br>

Where `fib` is an *uninterprented function* 
\begin{code}
{-@ measure fib :: Int -> Int @-}
\end{code}
<br>

We used `fib` to define the `axiom_fib`

\begin{code}
{-@ predicate Fib I = 
  (fib i) = (if (i <= 1) then 1 else ((fib (i-1)) + (fib (i-2))))
  @-}

{-@ assume axiom_fib :: i:Int -> {v: Bool | ((Prop v) <=> (Fib i))} @-}

axiom_fib :: Int -> Bool
axiom_fib i = undefined
\end{code}


Fast Fibonacci
--------------
Now we can efficiently compute the `i`th fibonacci number

\begin{code}
{-@ fastFib :: x:Int -> {v:Int | v = fib(x)} @-}
fastFib     :: Int -> Int
fastFib n   = snd $ fibMemo (V (\_ -> 0)) n
\end{code}

Fibonacci Memo
--------------

\begin{code}
{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = (fib i)}) @-}

fibMemo :: Vec Int -> Int -> (Vec Int, Int)
fibMemo t i 
  | i <= 1    
  = (t, liquidAssume (axiom_fib i) (1 :: Int))
  
  | otherwise 
  = case get i t of   
      0 -> let (t1, n1) = fibMemo t  (i-1)
               (t2, n2) = fibMemo t1 (i-2)
               n        = liquidAssume (axiom_fib i) (n1 + n2)
            in (set i n t2,  n)
      n -> (t, n)
\end{code}
