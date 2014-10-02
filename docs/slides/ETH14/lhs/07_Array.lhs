Abstract Refinements {#data}
============================

Recap
-----

**So far**

Abstract Refinements **decouple invariants** from *functions*

<br>

<div class="fragment">

**Next**

Decouple invariants from *indexed data structures*
</div>



Decouple Invariants From Data {#vector} 
=======================================

Example: Vectors 
----------------

<div class="hidden">
\begin{code}
module LiquidArray where

import Language.Haskell.Liquid.Prelude (liquidAssume, liquidError)

{-@ LIQUID "--no-termination" @-}
initialize :: Int -> Vec Int
\end{code}
</div>

<div class="fragment">

For this talk, implemented as maps from `Int` to `a` 

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

An alias for *segments* between `I` and `J`

<br>

\begin{code}
{-@ predicate Btwn I V J = I <= V && V < J @-}
\end{code}

</div>

Ex: Identity Vectors
--------------------

Defined between `[0..N)` mapping each key to itself:

<br>

<div class="fragment">

\begin{code}
{-@ type IdVec N = Vec <{\v -> (Btwn 0 v N)}, 
                        {\k v -> v = k}> 
                       Int                  @-}
\end{code}

</div>


Ex: Zero-Terminated Vectors
---------------------------

Defined between `[0..N)`, with *last* element equal to `0`:

<br>

<div class="fragment">

\begin{code}
{-@ type ZeroTerm N = 
     Vec <{\v -> Btwn 0 v N}, 
          {\k v -> k = N-1 => v = 0}> 
          Int                         @-}
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
          {\k v -> v = 0 || v = fib k}> 
          Int                          @-}
\end{code}


An API for Vectors
------------------

Next: Lets write an API for Vector operations

<br>

- `empty`

- `set`

- `get`


API: Empty Vectors
-----------------

`empty` a Vector whose domain is `false` (defined at *no* key)

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

API: `get` Key's Value 
----------------------

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


API: `set` Key's Value 
----------------------

- <div class="fragment">Input `key` in *domain*</div>

- <div class="fragment">Input `val` in *range* related with `key`</div>

- <div class="fragment">Input `vec` defined at *domain except at* `key`</div>

- <div class="fragment">Output domain *includes* `key`</div>

API: `set` Key's Value 
----------------------

\begin{code}
{-@ set :: forall a <d :: Int -> Prop,
                     r :: Int -> a -> Prop>.
           key: Int<d> -> val: a<r key>
        -> vec: Vec<{v:Int<d>| v /= key},r> a
        -> Vec <d, r> a                     @-}
set key val (V f) = V $ \k -> if k == key 
                                then val 
                                else f k
\end{code}

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Array.hs" target="_blank">Demo:</a>
Help! Can you spot and fix the errors? 
</div>

Using the Vector API
--------------------

Loop over vector, setting each key `i` equal to `i`:

\begin{code}
{-@ initialize :: n:Nat -> IdVec n @-}
initialize n      = loop 0 empty
  where
    loop i a 
      | i < n     = let a' = set i i a
                    in
                        loop (i+1) a'
      | otherwise = a 
\end{code}

Recap
-----

+ Created a `Vec` (Array) container 

+ Decoupled *domain* and *range* invariants from *data*

+ Enabled analysis of *array segments*

<br>

<div class="fragment">

Special purpose program analyses 

- [Gopan-Reps-Sagiv, POPL 05](link)
- [J.-McMillan, CAV 07](link)
- [Logozzo-Cousot-Cousot, POPL 11](link)
- [Dillig-Dillig, POPL 12](link) 
- ...

Encoded as an instance of abstract refinement types!
</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over Type Signatures
    + Functions
    + <div class="fragment">**Data**</div>

<div class="fragment">[[continue...]](11_Evaluation.lhs.slides.html)</div>
