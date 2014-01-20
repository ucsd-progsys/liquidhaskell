Abstract Refinements {#data}
============================

Recap
-----

**So far**

Decouple invariants from *functions*

<br>

<div class="fragment">

**Next**

Decouple invariants from *data structures*
</div>

Decouple Invariants From Data 
=============================

Example: Vectors 
----------------

<div class="hidden">
\begin{code}
module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume, liquidError)

{-@ LIQUID "--no-termination" @-}

fibMemo   :: Vec Int -> Int -> (Vec Int, Int)
fastFib   :: Int -> Int
idv       :: Int -> Vec Int
axiom_fib :: Int -> Bool
axiom_fib = undefined

{-@ predicate AxFib I = (fib I) == (if I <= 1 then 1 else fib(I-1) + fib(I-2)) @-}
\end{code}
</div>

<div class="fragment">

Implemented as maps from `Int` to `a` 

<br>

\begin{code}
data Vec a = V (Int -> a)
\end{code}

</div>


Abstract *Domain* and *Range*
-----------------------------

Parameterize type with *two* abstract refinements:

<br>

\begin{code}
{-@ data Vec a < dom :: Int -> Prop,
                 rng :: Int -> a -> Prop >
      = V {a :: i:Int<dom> -> a <rng i>}  @-}
\end{code}

<br>

- `dom`: *domain* on which `Vec` is *defined* 

- `rng`: *range*  and relationship with *index*

Abstract *Domain* and *Range*
-----------------------------

Diverse `Vec`tors by *instantiating* `dom` and `rng`

<br>

<div class="fragment">

A quick alias for *segments* between `I` and `J`

<br>

\begin{code}
{-@ predicate Seg V I J = (I <= V && V < J) @-}
\end{code}

</div>

Ex: Identity Vectors
--------------------

Defined between `[0..N)` mapping each key to itself:

<br>

<div class="fragment">

\begin{code}
{-@ type IdVec N = Vec <{\v -> (Seg v 0 N)}, 
                        {\k v -> v=k}> 
                       Int                  @-}
\end{code}

</div>

Ex: Identity Vectors
--------------------

Defined between `[0..N)` mapping each key to itself:

<br>

\begin{code}
{-@ idv :: n:Nat -> (IdVec n) @-}
idv n   = V (\k -> if 0 < k && k < n 
                     then k 
                     else liquidError "eeks")
\end{code}

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>Whats the problem? How can we fix it?
</div>

Ex: Zero-Terminated Vectors
---------------------------

Defined between `[0..N)`, with *last* element equal to `0`:

<br>

<div class="fragment">

\begin{code}
{-@ type ZeroTerm N = 
     Vec <{\v -> (Seg v 0 N)}, 
          {\k v -> (k = N-1 => v = 0)}> 
          Int                             @-}
\end{code}

</div>


Ex: Fibonacci Table 
-------------------

A vector whose value at index `k` is either 

- `0` (undefined), or, 

- `k`th fibonacci number 

\begin{code}
{-@ type FibV =  
     Vec <{\v -> true}, 
          {\k v -> (v = 0 || v = (fib k))}> 
          Int                               @-}
\end{code}


Accessing Vectors
-----------------

Next: lets *abstractly* type `Vec`tor operations, *e.g.* 

<br>

- `empty`

- `set`

- `get`


Ex: Empty Vectors
-----------------

`empty` returns Vector whose domain is `false`

<br>

\begin{code}
{-@ empty :: forall <p :: Int -> a -> Prop>. 
               Vec <{v:Int|false}, p> a     @-}

empty     = V $ \_ -> error "empty vector!"
\end{code}

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>
What would happen if we changed `false` to `true`?
</div>

Ex: `get` Key's Value 
---------------------

- *Input* `key` in *domain*

- *Output* value in *range* related with `k`

\begin{code}
{-@ get :: forall a <d :: Int -> Prop,  
                     r :: Int -> a -> Prop>.
           key:Int <d>
        -> vec:Vec <d, r> a
        -> a<r key>                        @-}

get k (V f) = f k
\end{code}


Ex: `set` Key's Value 
---------------------

- <div class="fragment">Input `key` in *domain*</div>

- <div class="fragment">Input `val` in *range* related with `key`</div>

- <div class="fragment">Input `vec` defined at *domain except at* `key`</div>

- <div class="fragment">Output domain *includes* `key`</div>

Ex: `set` Key's Value 
---------------------

\begin{code}
{-@ set :: forall a <d :: Int -> Prop,
                     r :: Int -> a -> Prop>.
           key: Int<d> -> val: a<r key>
        -> vec: Vec<{v:Int<d>| v /= key},r> a
        -> Vec <d, r> a                     @-}
set key val (V f) = V $ \k -> if k == key 
                                then val 
                                else f key
\end{code}

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>
Help! Can you spot and fix the errors? 
</div>

Using Vector API 
----------------

\begin{code}
{-@ loop :: forall a <p :: Int -> a -> Prop>.
        lo:Int 
     -> hi:{v:Int|lo <= v}
     -> base:a<p lo>                      
     -> f:(i:Int -> a<p i> -> a<p (i+1)>) 
     -> a<p hi>                           @-}

loop  :: Int -> Int -> α -> (Int -> α -> α) -> α
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc

\end{code}

Using Vector API 
----------------

\begin{code}
{-@ qualif Neqz(v:Int): v /= 0 @-}

{-@ initUpto :: Vec Int -> n:Nat -> (IdVec n) @-}
initUpto v n   = loop 0 n v (\i -> set i i)

-- initUpto :: Vec a -> a -> Int -> Vec a
-- initUpto a x n = loop 0 n empty (\i -> set i x)
\end{code}


Memoized Fibonacci
------------------

Lets use `Vec` to write a *memoized* fibonacci function

<br>

<div class="fragment">
\begin{code} Using the fibonacci table:
type FibV =  
     Vec <{\v -> true}, 
          {\k v -> (v = 0 || v = (fib k))}> 
          Int                              
\end{code}
</div>

<br>

<div class="fragment">
But wait, what is `fib` ?
</div>


Specifying Fibonacci
--------------------

`fib` is *uninterpreted* in the refinement logic  

<br>

\begin{code}
{-@ measure fib :: Int -> Int @-}
\end{code}

<br>

Specifying Fibonacci
--------------------

We *axiomatize* the definition of `fib` in SMT ...

\begin{code}<br>
predicate AxFib I = 
  (fib I) == if I <= 1 
               then 1 
               else fib(I-1) + fib(I-2)
\end{code}

Specifying Fibonacci
--------------------

Finally, lift axiom into LiquidHaskell as *ghost function*

<br>

\begin{code}
{-@ axiom_fib :: 
      i:_ -> {v:_|((Prop v) <=> (AxFib i))} @-}
\end{code}

<br>

<div class="fragment">
**Note:** Recipe for *escaping* SMT limitations

1. *Prove* fact externally
2. *Use* as ghost function call
</div>


Fast Fibonacci
--------------

An efficient fibonacci function

<br>

\begin{code}
{-@ fastFib :: n:Int -> {v:_ | v = (fib n)} @-}
fastFib n   = snd $ fibMemo (V (\_ -> 0)) n
\end{code}

<br>

<div class="fragment">
- `fibMemo` *takes* a table initialized with `0`

- `fibMemo` *returns* a table with `fib` values upto `n`.
</div>


Memoized Fibonacci 
------------------

\begin{code}
fibMemo t i 
  | i <= 1    
  = (t, liquidAssume (axiom_fib i) 1)
  | otherwise 
  = case get i t of   
     0 -> let (t1,n1) = fibMemo t  (i-1)
              (t2,n2) = fibMemo t1 (i-2)
              n       = liquidAssume 
                        (axiom_fib i) (n1+n2)
          in (set i n t2,  n)
     n -> (t, n)
\end{code}

Memoized Fibonacci 
------------------

- `fibMemo` *takes* a table initialized with `0`
- `fibMemo` *returns* a table with `fib` values upto `n`.

<br>

\begin{code}
{-@ fibMemo :: FibV 
            -> i:Int 
            -> (FibV,{v:Int | v = (fib i)}) @-}
\end{code}


