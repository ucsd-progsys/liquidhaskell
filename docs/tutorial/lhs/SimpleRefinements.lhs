% Simple Refinement Types

Simple Refinement Types
-----------------------

\begin{code}
module SimpleRefinements where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude
\end{code}


Simple Refinement Types
-----------------------

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

- `p1` **implies** `p2`

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

\begin{code} So we can have a type for natural numbers:

type Nat = {v:Int | v >= 0}
\end{code}

<br>

And we can type `0` as `Nat`:

<br>

\begin{code}
{-@ zero' :: Nat @-}
zero'     :: Int
zero'     =  0
\end{code}

Refinements are *logical formulas*
----------------------------------

Similarly, since

- `v = 0 => v mod 2 = 0` 

Therefore

- `{v:Int | v = 0} <: {v:Int | v mod 2 = 0}`

Thus, via SMT based subtyping LiquidHaskell verifies:

\begin{code}
{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ zero'' :: Even @-}
zero''     :: Int
zero''     =  0
\end{code}


Lists
-----

Refinements can live *inside* type constructors:

\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

Lists: Universal Invariants 
---------------------------

Constructors enable *universally quantified* invariants.

For example, *every element* in a list is non-negative:

\begin{code}
{-@ natList :: L Nat @-}
natList     :: L Int
natList     =  0 `C` 1 `C` 3 `C` N
\end{code}

or, *every element* in a list is even:

\begin{code}
{-@ evenList :: L Even @-}
evenList     :: L Int
evenList     =  0 `C` 2 `C` 8 `C` N
\end{code}


Refinement Function Types
-------------------------

Consider a `safeDiv` operator: <br>

\begin{code}
safeDiv    :: Int -> Int -> Int
safeDiv x y = x `div` y
\end{code}

We can use refinements to specify a **precondition**: divisor is **non-zero** <br>

\begin{code}
{-@ safeDiv :: Int -> {v:Int | v != 0} -> Int @-}
\end{code}

<br>

Demo

Dependent Function Types
------------------------

\begin{code} Consider a list indexing function:
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

We desire **precondition** that index `i` be between `0` and **list length**

Measuring A List's length in logic
----------------------------------

We define a **measure** for the length of a `List` <br>

\begin{code}
{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}
\end{code}

<br>

\begin{code} The measure strengthens the type of data constructors
data L a where 
  N :: {v : L a | (llen v) = 0}
  C :: a -> xs:(L a) -> {v:(L a) |(llen v) = 1 + (llen xs)}
\end{code}

Measuring A List's length in logic
----------------------------------

Now we can verify

<br>

\begin{code}
{-@ length :: xs:(L a) -> {v:Int | v = (llen xs)} @-}
length     :: L a -> Int
length N        = 0
length (C _ xs) = 1 + (length xs)
\end{code}

Measuring A List's length in logic
----------------------------------

And we can type `(!!)` as

<br>

\begin{code}
{-@ (!!) :: ls:(L a) -> {v:Nat | v < (llen ls)} -> a @-}
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

Demo: lets see what happens if we **change** the precondition
