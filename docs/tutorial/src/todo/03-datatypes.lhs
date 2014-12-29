Refined Data Types
==================

 
\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}

module SparseVectors (
   -- Sparse (..)
   -- , sparseProduct, sparseProduct'
   ) where

import Prelude      hiding (abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (foldl') 

-- sparseProduct, sparseProduct'  :: Vector Int -> Sparse Int -> Int
\end{code}
\end{comment}

So far, we have seen how to refine the types of *functions*, to
specify, for example, preconditions on the inputs, or postconditions
on the outputs.  Very often, we wish to create *datatypes* that
satisfy certain invariants; in these cases, it is handy to be able to
directly refine the the `data` definition, so that it is impossible to
create illegal inhabitants.


Often it is useful to specify i

Refining Data Types: Sparse Vectors
-----------------------------------

While the standard `Vector` is great for *dense* arrays,
often we have to manipulate *sparse* vectors where most
elements are just `0`. We might represent such vectors
as a list of index-value tuples:

\begin{code}
data Sparse a = SP { spSize  :: Int
                   , spElems :: [(Int, a)] } 
\end{code}

\noindent Implicitly, all indices *other* than those in the list
have the value `0` (or the equivalent value for the type `a`).

\newthought{Data Invariants} Unfortunately, Haskell's type system
does not make it easy to represent the fact that every *legal* `Sparse`
vector has indices that are between `0` and `spSize`. Fortunately, this is
easy to describe as a data type refinement in LiquidHaskell:

\begin{code}
{-@ data Sparse a = SP { spSize  :: Nat 
                       , spElems :: [(Btwn 0 spSize, a)]} @-}
\end{code}

\noindent In the above, we specify that `spSize` is non-negative,
and each index is indeed valid. Consequently LiquidHaskell verifies:

\begin{code}
okSP :: Sparse String
okSP= SP 5 [(0, "cat"), (3, "dog")]
\end{code}

\noindent but rejects:

\begin{code}
badSP :: Sparse String
badSP = SP 5 [(0, "cat"), (6, "dog")]
\end{code}

\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`; note that the field name
`spSize` are *measures*, like `vlen`, and can be used inside
refinements:

\begin{code}
{-@ type SparseN a N = {v:Sparse a | spSize v == N} @-} 
\end{code}

\noindent The alias `SparseN` is just a 
shorthand for the (longer) type on the right, it does not
*define* a new type. If you are familiar with the *index-style*
length encoding e.g. as found in [DML][dml] or [Agda][agdavec],
then note that despite  appearances, our `Sparse` definition
is *not* indexed.

\newthought{Sparse Products}
Lets write a function to compute a sparse product

\begin{code}
{-@ sparseProduct :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
sparseProduct x (SP _ y) = go 0 y
  where 
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y' 
    go sum []            = sum
\end{code}

LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the vector `x`, thereby
proving `x ! i` safe.

Refinements and Polymorphism
----------------------------

The sharp reader will have undoubtedly noticed that the sparse product 
can be more cleanly expressed as a [fold][foldl]:

\begin{spec}
foldl' :: (a -> b -> a) -> a -> [b] -> a
\end{spec}

\noindent We can simply fold over the sparse vector, accumulating the `sum`
as we go along

\begin{code}
{-@ sparseProduct' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
sparseProduct' x (SP _ y) = foldl' body 0 y   
  where 
    body sum (i, v)       = sum + (x ! i)  * v
\end{code}

\noindent
LiquidHaskell digests this too, without much difficulty. 
The main trick is in how the polymorphism of `foldl'` is instantiated. 

1. The GHC type inference engine deduces that at this site,
   the type variable `b` from the signature of `foldl'` is
   instantiated to the Haskell type `(Int, a)`. 

2. Correspondingly, LiquidHaskell infers that in fact `b`
   can be instantiated to the *refined* `(Btwn 0 v (vlen x), a)`. 

Thus, the inference mechanism saves us a fair bit of typing and allows us to
reuse existing polymorphic functions over containers and such without ceremony.

\newthought{Thats all} for now! Hopefully the above gives you
a reasonable idea of how one can use refinements to verify size
related properties, and more generally, to specify and verify
properties of recursive, and polymorphic functions operating
over datatypes. Read on to learn how we can teach LiquidHaskell
to reason about *structural* properties of data types.

[vecspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
[vec]:      http://hackage.haskell.org/package/vector
[dml]:      http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]:  http://code.haskell.org/Agda/examples/Vec.agda
[ref101]:   /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:   /blog/2013/01/27/refinements-101-reax.lhs/ 
[foldl]:    http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html
[listtail]: /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[dmlarray]: http://www.cs.bu.edu/~hwxi/academic/papers/pldi98.pdf

