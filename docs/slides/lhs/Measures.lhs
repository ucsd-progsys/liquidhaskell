% Measures

Measures
-----------------------

\begin{code}
module Measures where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude
\end{code}


Measuring A List's length in logic
----------------------------------

On `List` data type
\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

We define a **measure** for the length of a `List` <br>

\begin{code}
{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}
\end{code}

<br>

\begin{code} LiquidHaskell then **automatically strengthens** the types of data constructors
data L a where 
  N :: {v : L a | (llen v) = 0}
  C :: x:a -> xs:(L a) -> {v:(L a) |(llen v) = 1 + (llen xs)}
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
{-@ (!!)     :: ls:(L a) -> i:{v:Nat | v < (llen ls)} -> a @-}
(!!)         :: L a -> Int -> a
(C x _) !! 0 = x
(C _ xs)!! n = xs!!(n-1)
_       !! _ = liquidError "This should not happen!"
\end{code}

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellMeasure.hs" target= "_blank">Demo:</a> 
Lets see what happens if we **change** the precondition


Another measure for List
--------------------------

We define a new **measure** to check nullity of a `List` <br>

\begin{code}
{-@ measure isNull :: (L a) -> Prop
    isNull(N)      = true
    isNull(C x xs) = false
  @-}
\end{code}

<br>

\begin{code} LiquidHaskell then **automatically strengthens** the types of data constructors
data L a where 
  N :: {v : L a | isNull v}
  C :: x:a -> xs:(L a) -> {v:(L a) | not (isNull v)}
\end{code}



Multiple measures for List
--------------------------

The types of data constructors will be the **conjuction** of all the inferred types:


\begin{code} The types from `llen` definition
data L a where 
  N :: {v : L a | (llen v) = 0}
  C :: a -> xs: L a -> {v:L a |(llen v) = 1 + (llen xs)}
\end{code}

<br>
\begin{code} and the types from `isNull`
data L a where 
  N :: {v : L a | isNull v}
  C :: a -> xs: L a -> {v:L a | not (isNull v)}
\end{code}


<br>
\begin{code} So, the final types will be
data L a where 
  N :: {v : L a | (llen v) = 0 && (isNull v)}
  C :: a -> xs: L a -> {v:L a |(llen v) = 1 + (llen xs) && not (isNull v)}
\end{code}


Invariants in Data Constructors
------------------------------

We can refine the definition of data types setting **invariants**
\begin{code}
{-@ data L a = N
             | C (x :: a) (xs :: L {v:a | x <= v})  @-}
\end{code}

<br>

\begin{code} As before,the types of data constuctors are strengthened to
data L a where
  N :: L a
  C :: x:a -> xs: L {v:a | x <= v} -> L a
\end{code}

LiquidHaskell

- **Proves** the property when `C` is called

- **Assumes** the property when `C` is opened



Increasing Lists
-----------------

This invariant constrains all Lists to **increasing**
\begin{code}
{-@ data L a = N
             | C (x :: a) (xs :: L {v:a | x <= v})  @-}
\end{code}

<br>
<a href="http://goto.ucsd.edu:8090/index.html#?demo=HaskellInsertSort.hs"
target= "_blank">Insert sort</a> 
\begin{code}
{-@ insert :: Ord a => a -> L a -> L a @-}
insert :: Ord a => a -> L a -> L a
insert y (x `C` xs) | x <= y    = x `C` insert y xs
                    | otherwise = y `C` insert x xs

{-@ insertSort  :: Ord a => [a] -> L a @-}
insertSort  :: Ord a => [a] -> L a
insertSort = foldr insert N
\end{code}

<br>
What if increasing and decreasing lists should co-exist?

We use **abstract refinements** to allow it!
