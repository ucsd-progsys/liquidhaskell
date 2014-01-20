Abstract Refinements {#induction}
=================================

Induction
---------

Encoding *induction* with Abstract refinements

<div class="hidden">

\begin{code}
module Loop where
import Prelude hiding ((!!), foldr, length, (++))
-- import Measures
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}

{-@ measure llen  :: (L a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)  @-}

add   :: Int -> Int -> Int
loop  :: Int -> Int -> α -> (Int -> α -> α) -> α
foldr :: (L a -> a -> b -> b) -> b -> L a -> b
\end{code}
</div>

Induction
=========

Example: `loop` redux 
---------------------

Recall the *higher-order* `loop` 

<br>

\begin{code}
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

Iteration Dependence
--------------------

We used `loop` to write 

\begin{code} <br>
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

<br>

<div class="fragment">

**Problem**

- As property only holds after *last* loop iteration...

- ... cannot instantiate `α` with `{v:Int | v = n + m}`

</div>

Iteration Dependence
--------------------

We used `loop` to write 

\begin{code} <br>
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

<br>

**Problem** 

Need invariant relating *iteration* `i` with *accumulator* `acc`


Iteration Dependence
--------------------

We used `loop` to write 

\begin{code} <br>
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{code}

<br>

**Solution** 

- Abstract Refinement `p :: Int -> a -> Prop`

- `(p i acc)` relates *iteration* `i` with *accumulator* `acc`



Induction in `loop` (by hand)
-----------------------------

\begin{code} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

<div class="fragment">
<div align="center">

------------  ---   ----------------------------
  **Assume**   :    `out = loop lo hi base f` 

   **Prove**   :    `(p hi out)`
------------  ---   ----------------------------

</div>
</div>


Induction in `loop` (by hand)
-----------------------------

\begin{code} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

**Base Case** Initial accumulator `base` satisfies invariant


`(p base lo)`   


Induction in `loop` (by hand)
-----------------------------

\begin{code} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

**Inductive Step** `f` *preserves* invariant at `i`


`(p acc i) => (p (f i acc) (i + 1))`

Induction in `loop` (by hand)
-----------------------------

\begin{code} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{code}

<br>

**"By Induction"** `out` satisfies invariant at `hi` 

`(p out hi)`


Induction in `loop` (by type)
-----------------------------

Induction is an **abstract refinement type** for `loop` 

<br>

\begin{code}
{-@ loop :: forall a <p :: Int -> a -> Prop>.
        lo:Int 
     -> hi:{v:Int|lo <= v}
     -> base:a<p lo>                      
     -> f:(i:Int -> a<p i> -> a<p (i+1)>) 
     -> a<p hi>                           @-}
\end{code}

<br>

Induction in `loop` (by type)
-----------------------------

`p` is the index dependent invariant!


\begin{code}<br> 
p    :: Int -> a -> Prop             -- invt 
base :: a<p lo>                      -- base 
f    :: i:Int -> a<p i> -> a<p(i+1)> -- step
out  :: a<p hi>                      -- goal
\end{code}



Using Induction
---------------

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Nat| v=m+n} @-}
add n m = loop 0 m n (\_ z -> z + 1)
\end{code}

<br>

**Verified** by instantiating `loop`s abstract refinement 

`p := \i acc -> acc = i + n`


Using Induction
---------------

\begin{code} <div/>
{-@ add :: n:Nat -> m:Nat -> {v:Nat| v=m+n} @-}
add n m = loop 0 m n (\_ z -> z + 1)
\end{code}

<br>

Verified by instantiating `p := \i acc -> acc = i + n`

- **Base:**  `n = 0 + n`

- **Step:**  `acc = i + n  =>  acc + 1 = (i + 1) + n`

- **Goal:**  `out = m + n`


Generalizes To Structures 
-------------------------

Same idea applies for induction over *structures*

<br>

\begin{code}
data L a = N 
         | C a (L a)
\end{code}

Structural Induction
====================

Example: `foldr`
----------------

\begin{code}
{-@ foldr :: 
    forall a b <p :: L a -> b -> Prop>. 
      (xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)>) 
    -> b<p N> 
    -> ys:L a
    -> b<p ys>                            @-}
foldr f b N        = b
foldr f b (C x xs) = f xs x (foldr f b xs)
\end{code}

- **invariant** `(p xs b)` relates `b` with folded `xs`
- **base** `b` is related to empty list `N`
- **step** `f` extends relation from `xs` to `C x xs`
- **output** relation holds over entire list `ys`

Using `foldr`
-------------

We can now verify <br>

\begin{code}
{-@ size :: xs:L a -> {v: Int | v = (llen xs)} @-}
size :: L a -> Int
size = foldr (\_ _ n -> n + 1) 0
\end{code}

<br>

Here, the relation 

- `(p xs acc)` 

is **automatically instantiated** with

- `acc = (llen xs)`

Using `foldr`
-------------

Similarly we can now verify <br>

\begin{code}_
{-@ ++ :: xs:L a -> ys:L a -> {v:L a | (llen v) = (llen xs) + (llen ys)} @-} 
xs ++ ys = foldr (\_ z zs -> C z zs) ys xs 
\end{code}

<br>

Here, the relation 

- `(p xs acc)` 

is **automatically instantiated** with

- `(llen acc) = (llen xs) + (llen ys)`


