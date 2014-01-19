 {#abstractrefinements}
=======================

Abstracting Over Refinements
----------------------------

<div class="hidden">

\begin{code}
module AbstractRefinements where

import Prelude hiding (max)
import Language.Haskell.Liquid.Prelude
{-@ LIQUID "--no-termination" @-}
\end{code}

</div>

Abstracting Over Refinements
============================

Refined Data Constructors
-------------------------

**Example:** Increasing Lists, with strengthened constructors:

\begin{code} <br>
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{code}

<br>

<div class="fragment">**Problem:** What if we need *both* [increasing and decreasing lists](http://web.cecs.pdx.edu/~sheard/Code/QSort.html)?</div>

Problem Is Pervasive
--------------------


Example: Polymorphic `max` 
--------------------------

\begin{code} <br> 
max     :: a -> a -> a
max x y = if y <= x then x else y
\end{code}

<br>

\begin{code} We can instantiate `a` with `Odd`
max     :: Odd -> Odd -> Odd

maxOdd :: Odd
maxOdd = max 3 7
\end{code}


Polymorphic Max in Haskell
-----------------------

\begin{code} In Haskell the type of max is
max     :: Ord a => a -> a -> a
\end{code}


<br>

We could **ignore** the class constraints, and procced as before:

\begin{code} Instantiate `a` with `Odd`
max    :: Odd -> Odd -> Odd

maxOdd :: Odd
maxOdd = max 3 7
\end{code}


Polymorphic Add in Haskell
-----------------------

\begin{code} But this can lead to **unsoundness**:
max     :: Ord a => a -> a -> a
(+)     :: Num a => a -> a -> a
\end{code}

<br>

So, **ignoring** class constraints allows us to: 
\begin{code} instantiate `a` with `Odd`
(+)     :: Odd -> Odd -> Odd

addOdd :: Odd
addOdd = 3 + 7
\end{code}


Polymorphism via Parametric Invariants 
--------------------------------------

`max` returns *one of* its two inputs `x` and `y`. 

- **If** *both inputs* satisfy a property  

- **Then** *output* must satisfy that property

This holds, **regardless of what that property was!**
 
- That  is, we can **abstract over refinements**

- Or,  **parameterize** a type over its refinements.

Parametric Invariants
--------------------- 

\begin{code}
{-@ max :: forall <p :: a -> Prop>. Ord a => a<p> -> a<p> -> a<p> @-}
max     :: Ord a => a -> a -> a
max x y = if x <= y then y else x 
\end{code}



Where

- `a<p>` is just an abbreviation for `{v:a | (p v)}`


This type states explicitly:

- **For any property** `p`, that is a property of `a`, 

- `max` takes two **inputs** of which satisfy `p`,

- `max` returns an **output** that satisfies `p`. 



Using Abstract Refinements
--------------------------

- **If** we call `max` with two arguments with the same concrete refinement,

- **Then** the `p` will be instantiated with that concrete refinement,

- **The output** of the call will also enjoy the concrete refinement.


\begin{code}
{-@ type Odd = {v:Int | (v mod 2) = 1} @-}

{-@ maxOdd :: Odd @-}
maxOdd     :: Int
maxOdd     = max 3 5
\end{code}


Abstract Refinements in Type Constructors
-----------------------------------------

Types cannot track information of monomorphic arguments:

\begin{code}
data F = F {w::Int}
\end{code}

<br>

The type `F` cannot give us information about the field `x`.

\begin{code}
foo = let f = F 0 in -- :: f :: F
      case f of 
      F x -> liquidAssert (x >= 0)
\end{code}

<a href="http://goto.ucsd.edu:8090/index.html#?demo=AbstractRefinements.hs" target= "_blank">Demo:</a> 
Lets solve this error using Abstract Refinements

Abstract Refinements in Type Constructors
-----------------------------------------

- Abstract over the refinement you care
\begin{code}
data G = G {y::Int{- <p> -}}
\end{code}

- Move it to the left-hand side
\begin{code}
{-@ data G <p :: Int -> Prop> = G (y::Int<p>) @-}
\end{code}

- The type `G <p>` now describes the field `x`.

\begin{code}
bar = let f = G 0 in -- :: f :: G <{v = 0}>
      case f of 
      G x -> liquidAssert (x >= 0)
\end{code}

Abstract Refinements in Lists
-----------------------------------------

\begin{code} Remember increasing Lists?
data IL a = N | C (x :: a) (xs :: L {v:a | x <= v})
\end{code}

- Abstract over the refinement you care
\begin{code}
data L a = N | C {x :: a, xs :: L a {- v:a | p v x -}}
\end{code}

- Move it to the left-hand side
\begin{code}
{-@ data L a <p :: a -> a -> Prop> = 
      N 
    | C (x :: a) (xs :: L <p> a<p x>)  @-}
\end{code}

<br>

We can get back increasing Lists:
\begin{code}
{-@ type IncrL a = L <{\x v -> x <= v}> a @-}
\end{code}


Multiple Instantiations
-----------------------

\begin{code} Now increasing lists 
type IncrL a = L <{\x v -> x <= v}> a
\end{code}

<br>

\begin{code} Co-exist with decreasing ones
type DecrL a = L <{\x v -> x >= v}> a
\end{code}

Ghc Sort
--------

We can now verify algorithms that use **both** increasing and decreasing lists

\begin{code}
{-@ type OList a = [a]<{\hd v -> hd <= v}> @-}

{-@ sort :: (Ord a) => [a] -> OList a  @-}
sort :: (Ord a) => [a] -> [a]
sort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs
\end{code}

Ghc Sort : Helper Functions
---------------------------

\begin{code}
mergeAll [x] = x
mergeAll xs  = mergeAll (mergePairs xs)

mergePairs (a:b:xs) = merge1 a b: mergePairs xs
mergePairs [x]      = [x]
mergePairs []       = []

merge1 (a:as') (b:bs')
  | a `compare` b == GT = b : merge1 (a:as')  bs'
  | otherwise           = a : merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as
\end{code}
