Abstract Refinements {#induction}
=================================

Decoupling Invariants & Code
----------------------------

<br>

Abstract refinements decouple invariants from code

<br>

<div class="fragment">

**Next:** Precise Specifications for HOFs

<div class="hidden">

\begin{code}
module Loop where
import Prelude hiding ((!!), foldr, length, (++))
import Data.Set hiding (insert, foldr,size,filter, append) 

-- import Measures
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

{-@ measure size  :: (L a) -> Int
    size (N)      = 0
    size (C x xs) = 1 + (size xs)  @-}

{-@ measure elems :: L a -> (Set a)
    elems (N)      = (Set_empty 0)
    elems (C x xs) = (Set_cup (Set_sng x) (elems xs))
  @-}

{-@ type UnElems Xs Ys = {v:_ | elems v = Set_cup (elems Xs) (elems Ys)} @-}

size  :: L a -> Int
add    :: Int -> Int -> Int
loop   :: Int -> Int -> α -> (Int -> α -> α) -> α
ifoldr :: (L a -> a -> b -> b) -> b -> L a -> b

\end{code}
</div>

<!-- BEGIN CUT

Induction
=========

Example: A Higher Order `loop` 
-------------------------------


<br>
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

We can use `loop` to write 

<br>

\begin{spec} 
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop' 0 m n (\_ i -> i + 1)
\end{spec}

<br>

<div class="fragment">

**Problem** But cannot prove `add n m :: {v:_ | v = n + m}`

- As property only holds after *last* loop iteration...

- ... cannot instantiate `α` with `{v:Int | v = n + m}`

</div>

Iteration Dependence
--------------------

We used `loop` to write 

<br>

\begin{spec} 
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{spec}

<br>

**Problem** 

Need invariant relating *iteration* `i` with *accumulator* `acc`


Iteration Dependence
--------------------

We used `loop` to write 

\begin{spec} <br>
{-@ add :: n:Nat -> m:Nat -> {v:Nat|v=m+n} @-}
add n m = loop 0 m n (\_ i -> i + 1)
\end{spec}

<br>

**Solution** 

- Abstract Refinement `p :: Int -> a -> Prop`

- `(p i acc)` relates *iteration* `i` with *accumulator* `acc`



Induction in `loop` (by hand)
-----------------------------

\begin{code} 
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

\begin{spec} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{spec}

<br>

**Base Case:** &nbsp; Initial accumulator `base` satisfies invariant


`(p lo base)`   


Induction in `loop` (by hand)
-----------------------------

\begin{spec} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{spec}

<br>

**Inductive Step:** &nbsp; `f` *preserves* invariant at `i`


`(p i acc) => (p (i+1) (f i acc))`

Induction in `loop` (by hand)
-----------------------------

\begin{spec} <br> 
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
\end{spec}

<br>

**"By Induction"** &nbsp; `out` satisfies invariant at `hi` 

`(p hi out)`


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


\begin{spec}<br> 
p    :: Int -> a -> Prop             -- invt 
base :: a<p lo>                      -- base 
f    :: i:Int -> a<p i> -> a<p(i+1)> -- step
out  :: a<p hi>                      -- goal
\end{spec}



Using Induction
---------------

\begin{code}
{-@ add :: n:Nat -> m:Nat -> {v:Nat| v=m+n} @-}
add n m = loop 0 m n (\_ z -> z + 1)
\end{code}

<br>

**Verified** by *instantiating* the abstract refinement of `loop`

`p := \i acc -> acc = i + n`


Generalizes To Structures 
-------------------------

Same idea applies for induction over *structures* ...

<br>
<br>

[DEMO 02_AbstractRefinements.hs #2](../hs/02_AbstractRefinements.hs) 


END CUT -->


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
Lets write a generic loop over lists ...
</div>


Example: `foldr`
----------------

<br>
<br>

\begin{code}
foldr :: (α -> β -> β) -> β -> L α -> β
foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)
\end{code}


Problem
-------

Recall our *failed attempt* to write `append` with `foldr`

<br>

\begin{spec} 
{-@ app :: xs:_ -> ys:_ -> UnElems xs ys @-}
app xs ys = foldr C ys xs
\end{spec}

<br>

<div class="fragment">
- Property holds after *last* iteration
- Cannot instantiate `α` with `UnElems xs ys`
</div>

Problem
-------

Recall our *failed attempt* to write `append` with `foldr`

<br>

\begin{spec} 
{-@ app :: xs:_ -> ys:_ -> UnElems xs ys @-}
app xs ys = foldr C ys xs
\end{spec}


<br>

Need to **relate** each *iteration* with *accumulator* `acc` 




Solution: Inductive `foldr`
---------------------------

<br>
<br>

<div class="fragment">
Lets brace ourselves for the type...
</div>

Solution: Inductive `foldr`
---------------------------

\begin{code}
{-@ ifoldr :: 
     forall a b <p :: L a -> b -> Prop>. 
      (xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)>) 
    -> b<p N> 
    -> ys:L a
    -> b<p ys>                            @-}
ifoldr f b N        = b
ifoldr f b (C x xs) = f xs x (ifoldr f b xs)
\end{code}

<br>

<div class="fragment">
Lets step through the type...
</div>


`ifoldr`: Abstract Refinement
-----------------------------

\begin{spec} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  ::  b<p ys>                            
\end{spec}

<br>

`(p xs b)` relates `b` with **folded** `xs`

`p :: L a -> b -> Prop`


`ifoldr`: Base Case
-------------------

\begin{spec} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{spec}

<br>

`base` is related to **empty** list `N`

`base :: b<p N>` 



`ifoldr`: Ind. Step 
-------------------

\begin{spec} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{spec}

<br>

`step` **extends** relation from `xs` to `C x xs`

`step :: xs:_ -> x:_ -> b<p xs> -> b<p (C x xs)>`


`ifoldr`: Output
----------------

\begin{spec} <div/>
p    :: L a -> b -> Prop   
step :: xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)> 
base :: b<p N> 
ys   :: L a
out  :: b<p ys>                            
\end{spec}

<br>

Hence, relation holds between `out` and **entire input** list `ys`

`out :: b<p ys>`

Using `ifoldr`: Size
-------------------

We can now verify

<br>

\begin{code}
{-@ size :: xs:_ -> {v:Int| v = size xs} @-}
size     = ifoldr (\_ _ n -> n + 1) 0
\end{code}

<br>

<div class="fragment">
by *automatically instantiating* `p` with

`\xs acc -> acc = size xs`
</div>

Using `foldr`: Append
---------------------

We can now verify

<br>

\begin{code}
{-@ (++) :: xs:_ -> ys:_ -> UnElems xs ys @-} 
xs ++ ys = ifoldr (\_ -> C) ys xs 
\end{code}

<br>

<br>

<div class="fragment">
By *automatically* instantiating `p` with

`\xs acc -> elems acc = Set_cup (elems xs) (elems ys)`

</div>

More Examples
-------------

Induction over *structures* from `GHC.List`

<br>

+ `length`
+ `append`
+ `filter`
+ ...

<br>

[DEMO 02_AbstractRefinements.hs #2](../hs/02_AbstractRefinements.hs) 



Recap
-----

<br>

Abstract refinements *decouple* **invariant** from **iteration**

<br>

<div class="fragment">**Precise** specs for higher-order functions.</div>

<br>

<div class="fragment">**Automatic** checking and instantiation by SMT.</div>

Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract: Refinements over Type Signatures
    + <div class="fragment">**Functions**</div>
    + <div class="fragment">**Recursive Data** <a href="08_Recursive.lhs.slides.html" target="_blank">[continue]</a></div>
5. <div class="fragment">[Evaluation](11_Evaluation.lhs.slides.html)</div>
