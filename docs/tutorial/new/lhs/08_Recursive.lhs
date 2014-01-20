Decouple Invariants From Data {#recursive} 
==========================================

Recursive Structures 
--------------------

<div class="fragment">
Lets see another example of decoupling...
</div>

<div class="hidden">
\begin{code}
module List where

{-@ LIQUID "--no-termination" @-}

infixr `C`
\end{code}
</div>

Decouple Invariants From Recursive Data
=======================================

Recall: Lists
-------------

\begin{code}
data L a = N 
         | C a (L a)
\end{code}


Recall: Refined Constructors 
----------------------------

Define *increasing* Lists with strengthened constructors:

\begin{code} <br>
data L a where
  N :: L a
  C :: hd:a -> tl: L {v:a | hd <= v} -> L a
\end{code}

Problem: Decreasing Lists?
--------------------------

What if we need *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?

<br>

<div class="fragment">
*Separate* types are tedious...
</div>


Abstract That Refinement!
-------------------------

\begin{code}
{-@ data L a <p :: a -> a -> Prop>
      = N 
      | C (hd :: a) (tl :: (L <p> a<p hd>)) @-}
\end{code}

<br>

- <div class="fragment"> `p` is a *binary* relation between two `a` values</div>

- <div class="fragment"> Definition relates `hd` with *all* the elements of `tl`</div>

- <div class="fragment"> Recursive: `p` holds for *every pair* of elements!</div>

Example
-------

Consider a list with *three* or more elements 

\begin{code} <br>
x1 `C` x2 `C` x3 `C` rest :: L <p> a 
\end{code}

Example: Unfold Once
--------------------

\begin{code} <br> 
x1                 :: a
x2 `C` x3 `C` rest :: L <p> a<p x1> 
\end{code}

Example: Unfold Twice
---------------------

\begin{code} <br> 
x1          :: a
x2          :: a<p x1>  
x3 `C` rest :: L <p> a<p x1 && p x2> 
\end{code}

Example: Unfold Thrice
----------------------

\begin{code} <br> 
x1   :: a
x2   :: a<p x1>  
x3   :: a<p x1 && p x2>  
rest :: L <p> a<p x1 && p x2 && p x3> 
\end{code}

<br>

<div class="fragment">
Note how `p` holds between **every pair** of elements in the list. 
</div>

A Concrete Example
------------------

That was a rather *abstract*!

<br>

How can we *use* fact that `p` holds between *every pair* ?


Using Recursive Refinements 
---------------------------

*Instantiate* `p` with a *concrete* refinement

<br>

\begin{code}
{-@ type IncL a = L <{\hd v -> hd <= v}> a @-}
\end{code}

- The refinement says `hd` is less than the arbitrary tail element `v`.

- Thus `SL` denotes lists sorted in **increasing order**!




