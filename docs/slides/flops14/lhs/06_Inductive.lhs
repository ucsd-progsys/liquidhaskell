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

size  :: L a -> Int
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

**Base Case:** &nbsp; Initial accumulator `base` satisfies invariant


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

**Inductive Step:** &nbsp; `f` *preserves* invariant at `i`


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

**"By Induction"** &nbsp; `out` satisfies invariant at `hi` 

`(p out hi)`


Induction in `loop` (by type)
-----------------------------

Induction is an **abstract refinement type** for `loop` 

<br>

\begin{code}
{-@ loop :: forall a <p :: Int -> a -> Prop>.
        lo:Int
     -> hi:{Int | lo <= hi}
     -> base:a<p lo>                      
     -> f:(i:Int -> a<p i> -> a<p (i+1)>) 
     -> a<p hi>                           @-}
\end{code}

<br>

Induction in `loop` (by type)
-----------------------------

`p` is the *index dependent* invariant!


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

**Verified** by instantiating the abstract refinement of `loop`

`p := \i acc -> acc = i + n`


Using Induction
---------------

\begin{code} <div/>
{-@ add :: n:Nat -> m:Nat -> {v:Nat| v=m+n} @-}
add n m = loop 0 m n (\_ z -> z + 1)
\end{code}

<br>

Verified by instantiating `p := \i acc -> acc = i + n`

- <div class="fragment">**Base:**  `n = 0 + n`</div>

- <div class="fragment">**Step:**  `acc = i + n  =>  acc + 1 = (i + 1) + n`</div>

- <div class="fragment">**Goal:**  `out = m + n`</div>


Generalizes To Structures 
-------------------------

Same idea applies for induction over *structures* ...


Structural Induction
====================

Example: Lists
--------------

<br>

\begin{code}
data L a = N 
         | C a (L a)
\end{code}

<br>

<div class="fragment">
Lets write a generic loop over such lists ...
</div>

Example: `foldr`
----------------

\begin{code} <br>
foldr f b N        = b
foldr f b (C x xs) = f xs x (foldr f b xs)
\end{code}

<br>

<div class="fragment">
Lets brace ourselves for the type...
</div>

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

<br>

<div class="fragment">
Lets step through the type...
</div>


`foldr`: Abstract Refinement
----------------------------

\begin{code} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  ::  b<p ys>                            
\end{code}

<br>

`(p xs b)` relates `b` with **folded** `xs`

`p :: L a -> b -> Prop`


`foldr`: Base Case
------------------

\begin{code} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{code}

<br>

`base` is related to empty list `N`

`base :: b<p N>` 



`foldr`: Ind. Step 
------------------

\begin{code} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{code}

<br>

`step` extends relation from `xs` to `C x xs`

`step :: xs:L a -> x:a -> b<p xs> -> b<p(C x xs)>`


`foldr`: Output
---------------

\begin{code} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{code}

<br>

Relation holds between `out` and input list `ys`

`out :: b<p ys>`

Using `foldr`: Size
-------------------

We can now verify <br>

\begin{code}
{-@ size :: xs:_ -> {v:Int| v = (llen xs)} @-}
size     = foldr (\_ _ n -> n + 1) 0
\end{code}

<br>

<div class="fragment">
by *automatically instantiating*

`p := \xs acc -> acc = (llen xs)`
</div>

Using `foldr`: Append
---------------------

\begin{code}
{-@ (++) :: xs:_ -> ys:_ -> (Cat a xs ys) @-} 
xs ++ ys = foldr (\_ -> C) ys xs 
\end{code}

<br>

<div class="fragment">

where the alias `Cat` is:

<br>

\begin{code}
{-@ type Cat a X Y = 
    {v:_|(llen v) = (llen X) + (llen Y)} @-}
\end{code}

</div>

Using `foldr`: Append
---------------------

\begin{code} <div/>
{-@ (++) :: xs:_ -> ys:_ -> (Cat a xs ys) @-} 
xs ++ ys = foldr (\_ -> C) ys xs 
\end{code}

<br>

<div class="fragment">

Verified by automatically instantiating 

`p := \xs acc -> llen acc = llen xs + llen ys`

</div>

Recap
-----

Abstract refinements *decouple* **invariant** from **traversal**

<br>

<div class="fragment">**Reusable** specifications for higher-order functions.</div>

<br>

<div class="fragment">**Automatic** checking and instantiation by SMT.</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over Type Signatures
    + <div class="fragment">**Functions**</div>
    + <div class="fragment">**Data** <a href="08_Recursive.lhs.slides.html" target="_blank">[continue]</a></div>

