Simple Refinement Types {#simplerefinements}
=======================


Simple Refinement Types
-----------------------

\begin{code}
module SimpleRefinements where
import Language.Haskell.Liquid.Prelude
\end{code}


Simple Refinement Types
-----------------------

We use special comments to give specifications, 
as *refinement types*.

This type describes `Int` values that equal `0`.


\begin{code}
{-@ zero :: {v:Int | v = 0} @-}
zero     :: Int
zero     =  0
\end{code}

Refinements are *logical formulas*
----------------------------------

If 

- refinement of `T1` **implies** refinement of `T2` 

- `p1 => p2`

Then

- `T1` is a **subtype** of `T2`

- `{v:t | p1} <: {v:t | p2}`

Refinements are *logical formulas*
----------------------------------

For example, since

- `v = 0` *implies* `v >= 0`

Therefore
 
- `{v:Int | v = 0} <: {v:Int | v >= 0}`


Refinements are *logical formulas*
----------------------------------

\begin{code} So we can have a type for natural numbers: <br>
type Nat = {v:Int | v >= 0}
\end{code}

<br>

And, via SMT based subtyping LiquidHaskell verifies:

<br>

\begin{code}
{-@ zero' :: Nat @-}
zero'     :: Int
zero'     =  0
\end{code}


Lists: Universal Invariants 
---------------------------

Constructors enable *universally quantified* invariants.

For example, we define a list:

\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

<br>

And specify that, *every element* in a list is non-negative:

\begin{code}
{-@ natList :: L Nat @-}
natList     :: L Int
natList     =  0 `C` 1 `C` 3 `C` N
\end{code}

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if `natList` contained a negative number. 

Refinement Function Types
-------------------------

Consider a `safeDiv` operator: <br>

\begin{code}
safeDiv    :: Int -> Int -> Int
safeDiv x y = x `div` y
\end{code}

<br>
We can use refinements to specify a **precondition**: divisor is **non-zero** <br>

\begin{code}
{-@ safeDiv :: Int -> {v:Int | v != 0} -> Int @-}
\end{code}

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellSimpleRefinements.hs" target= "_blank">Demo:</a> 
Lets see what happens if the preconditions cannot be
proven. 

Dependent Function Types
------------------------

\begin{code} Consider a list indexing function:
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

We desire a **precondition** that index `i` be between `0` and **list length**.

We use **measures** to talk about the length of a list in **logic**.


