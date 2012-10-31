Index-Dependent Invariants
==========================

In this example, we illustrate how abstract invariants allow us to specify and verify index-dependent invariants of key-value maps. 
To this end, we develop a small library of _extensible vectors_ encoded, for purposes of illustration, as functions from `Int` to some generic range `a`. 

\begin{code}
module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume)
\end{code}

\begin{code}We specify vectors as 
type Vec a <dom :: Int -> Bool, rng :: Int -> a -> Bool>
  = (i:Int <dom> -> a<rng i>)
\end{code}

\begin{code}
type Vec a = Int -> a
\end{code}

Here, we are parametrizing the definition of the type `Vec` with _two_ abstract refinements, `dom` and `rng`, which respectively describe the _domain_ and _range_ of the vector.
That is, `dom` describes the set of _valid_ indices, and `rng` specifies an invariant relating each `Int` index with the value stored at that index.

Creating Vectors
----------------

We can use the following basic functions to create vectors:

\begin{code}
{-@ empty :: forall <rng :: Int -> a -> Bool>. 
              i:{v: Int | 0 = 1} ->  a<rng> @-}
empty :: Vec a
empty = \_ -> (error "Empty Vec")

{-@ create :: x:a -> (i:Int -> {v:a | v = x}) @-}
create :: a -> Vec a
create x = (\_ -> x)
\end{code}

The signature for `empty` states that its domain is empty (ie is the set of indices satisfying the predicate `False`), and that the range satisfies _any_ invariant. The signature for `create`, instead, defines a _constant_ vector that maps every index to the constant `x`.

Accessing Vectors
-----------------

We can write the following `get` function for reading the contents of a vector at a given index:

\begin{code}
{-@ get :: forall a <d :: x0:Int -> Bool, r :: x0: Int -> x1:a -> Bool>.
             i: Int<d> ->
             a: (j: Int<d> -> a<r j>) ->
             a<r i> 
  @-}
get :: Int -> Vec a -> a
get i a = a i
\end{code}

The signature states that for any domain `d` and range `r`, if the index `i` is a valid index, ie is of type, `Int<d>` then the returned value is an `a` that additionally satisfies the range refinement at the index `i`.

The type for `set`, which _updates_ the vector at a given index, is even more interesting, as it allows us to _extend_ the domain of the vector:

\begin{code}
{-@ set :: forall a <r :: x0: Int -> x1: a -> Bool, d :: x0: Int -> Bool>.
      i: Int<d> ->
      x: a<r i> ->
      a: (j: {v: Int<d> | v != i} -> a<r j>) ->
      (k : Int<d> -> a<r k>)
  @-}
set :: Int -> a -> Vec a -> Vec a
set i x a = \k -> if k == i then x else a k
\end{code}

The signature for `set` requires that (a) the input vector is defined everywhere at `d` _except_ the index `i`, and (b) the value supplied must be of type `a<r i>`, ie satisfy the range relation at the index `i` at which the vector is being updated.
The signature ensures that the output vector is defined at `d` and each value satisfies the index-dependent range refinement `r`.

Note that it is legal to call `get` with a vector that is _also_ defined at the index `i` since, by contravariance, such a vector is a subtype of that required by (a).


Initializing Vectors
--------------------

Next, we can write the following function, `init`, that ''loops'' over a vector, to `set` each index to a value given by some function.

\begin{code}
{-@ initialize :: forall a <r :: x0: Int -> x1: a -> Bool>.
      f: (z: Int -> a<r z>) ->
      i: {v: Int | v >= 0} ->
      n: Int ->
      a: (j: {v: Int | (0 <= v && v < i)} -> a<r j>) ->
      (k: {v: Int | (0 <= v && v < n)} -> a<r k>) @-}
initialize :: (Int -> a) -> Int -> Int -> Vec a -> Vec a
initialize f i n a 
  | i >= n    = a
  | otherwise = initialize f (i + 1) n (set i (f i) a)
\end{code}

The signature requires that (a) the higher-order function `f` produces values that satisfy the range refinement `r`, and (b) the vector is initialized from `0` to `i`.
The function ensures that the output vector is initialized from `0`
through `n`.

We can thus verify that

\begin{code}
{-@ idVec :: n:Int -> (k: {v: Int | (0 <= v && v < n)} -> {v: Int | v = k}) @-}
idVec :: Int -> (Vec Int)
idVec n = initialize (\i -> i) 0 n empty
\end{code}

ie `idVec` returns an vector of size `n` where each key is mapped to itself. Thus, abstract refinement types allow us to verify low-level idioms such as the incremental initialization of vectors, which have previously required special analyses.

Null-Terminated Strings
-----------------------

We can also use abstract refinements to verify code which manipulates C-style null-terminated strings, where each character is represented as an `Int` and the termination character `\0`, and only that, is represented as `0`.

\begin{code}Formally, a null-terminated string, represented by `Int`s, of size `n` has the type
type NullTerm n 
     = Vec <{\v -> 0<=v<n}, {\i v -> i=n-1 => v=0}> Int
\end{code}

The above type describes a length-`n` vector of characters whose last element must be a null character, signalling the end of the string.

We can use this type in the specification of a function, `upperCase`, which iterates through the characters of a string, uppercasing each one until it encounters the null terminator:

\begin{code}
ucs :: Int -> Int -> Vec Int -> Vec Int
ucs n i s =
  case get i s of
  0 -> s
  c -> ucs n (i + 1) (set i (c + 32) s)

{-@ upperCaseString ::
      n: {v: Int | v > 0} ->
      s: (j: {v : Int | (0 <= v && v < n)} ->
          {v: Int | (j = n - 1 => v = 0)}) ->
      (j: {v : Int | (0 <= v && v < n)} ->
       {v: Int | (j = n - 1 => v = 0)})
@-}
upperCaseString :: Int -> Vec Int -> Vec Int
upperCaseString n s = ucs n 0 s
\end{code}


Note that the length parameter `n` is provided solely as a ''witness'' for the length of the string `s`, which allows us to use the length of `s` in the type of `upperCaseString`; `n` is not used in the computation.

In order to establish that each call to `get` accesses string `s` within its bounds, our type system must establish that, at each call to the inner function `ucs`, `i` satisfies the type `{v: Int | 0 <= v && v < n}`.

This invariant is established as follows:

First, the invariant trivially holds on the first call to `ucs`, as
`n` is positive and `i` is `0`.
Second, we assume that `i` satisfies the type `{v: Int | 0 <= v && v < n}`, and, further, we know from the types of `s` and `get` that `c` has the type `{v: Int | i = n - 1 => c = 0}`.
Thus, if `c` is non-null, then `i` cannot be equal to `n - 1`.
This allows us to strengthen our type for `i` in the else branch to `{v: Int | 0 <= v && v < n - 1}` and thus to conclude that the value `i + 1` recursively passed as the `i` parameter to `ucs` satisfies the type `{v: Int | 0 <= v && v < n}`, establishing the inductive invariant and thus the safety of the `upperCaseString` function.



Memoization 
-----------

Next, let us illustrate how the same expressive signatures allow us to verify memoizing functions. We can specify to the SMT solver the definition of the Fibonacci function via an uninterpreted function `fib` and an axiom:

\begin{code}
{-@ measure fib :: Int -> Int @-}

{-@ axiom_fib :: i:Int -> {v: Bool | ((? v) <=> 
                            (fib(i) = ((i <= 1) ? 1 : ((fib(i-1)) + (fib(i-2))))))} 
  @-}
axiom_fib :: Int -> Bool
axiom_fib i = undefined
\end{code}

Next, we define a type alias `FibV` for the vector whose values are either `0` (ie undefined), or equal to the Fibonacci number of the corresponding index. 

\begin{code}
{-@ type FibV = j:Int -> {v:Int| ((v != 0) => (v = fib(j)))} @-}
\end{code}

Finally, we can use the above alias to verify `fastFib`, an implementation of the Fibonacci function, which uses an vector memoize intermediate results 

\begin{code}
{-@ fastFib :: x:Int -> {v:Int | v = fib(x)} @-}
fastFib     :: Int -> Int
fastFib n   = snd $ fibMemo (\_ -> 0) n

{-@ fibMemo :: FibV -> i:Int -> (FibV, {v: Int | v = fib(i)}) @-}
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

Thus, abstract refinements allow us to define key-value maps with index-dependent refinements for the domain and range. 
Quantification over the domain and range refinements allows us to define generic access operations (eg. `get`, `set`, `create`, `empty`) whose types enable us establish a variety of precise invariants.




