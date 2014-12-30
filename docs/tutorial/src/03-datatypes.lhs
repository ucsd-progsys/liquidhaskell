Refined Datatypes
=================

 
\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}

module RefinedDatatypes
       (
         -- * Sparse: Data
         Sparse (..)

         -- * Sparse: Functions
       , dotProd, dotProd', add, fromList  

         -- * Sparse: Examples
       , okSP, badSP, test1, test2
 
          -- * OrdList: Data
       , IncList  (..)

          -- * OrdList: Examples
       , okList, badList 
       )
      where

import Prelude      hiding (abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (foldl', fromList) 
import Data.Maybe   (fromJust)

dotProd, dotProd' :: Vector Int -> Sparse Int -> Int
test1 :: Sparse String
test2 :: Sparse Int

\end{code}
\end{comment}

So far, we have seen how to refine the types of *functions*, to
specify, for example, preconditions on the inputs, or postconditions
on the outputs. Very often, we wish to define *datatypes* that satisfy
certain invariants. In these cases, it is handy to be able to directly
refine the the `data` definition, so that it is impossible to create
illegal inhabitants.

Sparse Vectors Revisited {#sparsedata}
-------------------------------------

As our first example of a refined datatype, lets revisit the
sparse vector representation that we [saw earlier](#sparsetype).
The `SparseN` type alias we used got the job done, but is not
pleasant to work with because we have no way of determining
the *dimension* of the sparse vector. Instead, lets create a new
datatype to represent such vectors:

\begin{code}
data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] } 
\end{code}

\noindent
Thus, a sparse vector is a pair of a dimension and a list of
index-value tuples. Implicitly, all indices *other* than those
in the list have the value `0` or the equivalent value type `a`.

\newthought{Legal}
`Sparse` vectors satisfy two crucial properties.
First, the dimension stored in `spDim` is non-negative.
Second, every index in `spElems` must be valid, i.e.
between `0` and the dimension. Unfortunately, Haskell's
type system does not make it easy to ensure that
*illegal vectors are not representable*.
\footnotetext{The standard approach is to use abstract types and
[smart constructors](https://www.haskell.org/haskellwiki/Smart_constructors)
but even then there is only the informal guarantee that the
smart constructor establishes the right invariants.}

\newthought{Data Invariants} LiquidHaskell lets us enforce
these invariants with a refined data definition:

\begin{code}
{-@ data Sparse a = SP { spDim   :: Nat 
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
\end{code}

\noindent Where, as before, the we use the aliases:

\begin{code}
{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
\end{code}

\newthought{Refined Data Constructors} The refined data
definition is internally converted into refined types
for the data constructor `SP`:

\begin{spec}
-- Generated Internal representation
data Sparse a where
  SP :: spDim:Nat -> spElems:[(Btwn 0 spDim, a)] -> Sparse a 
\end{spec}

\noindent In other words, by using refined input types for `SP`
we have automatically converted it into a *smart* constructor that
ensures that *every* instance of a `Sparse` is legal.
Consequently, LiquidHaskell verifies:

\begin{code}
okSP :: Sparse String
okSP = SP 5 [(0, "cat"), (3, "dog")]
\end{code}

\noindent but rejects, due to the invalid index:

\begin{code}
badSP :: Sparse String
badSP = SP 5 [(0, "cat"), (6, "dog")]
\end{code}

\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. We can use the field name
`spDim` as a *measure*, like `vlen`. That is, we can use `spDim`
inside refinements:

\begin{code}
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-} 
\end{code}

\noindent As before, the alias `SparseN` is an alias for
the (longer) type on the right; it does not *define* a new type.
\footnote{Unlike the representations found in [DML][dml] or
[Agda][agdavec], our `SparseN` definition is *not* an indexed type.}

\newthought{Sparse Products}
Lets write a function to compute a sparse product

\begin{code}
{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd x (SP _ y) = go 0 y
  where 
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y' 
    go sum []            = sum
\end{code}

LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the vector `x`, thereby
proving `x ! i` safe.

\newthought{Folded Product} We can port the `fold`-based product
to our new representation:

\begin{code}
{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' x (SP _ y) = foldl' body 0 y   
  where 
    body sum (i, v)       = sum + (x ! i)  * v
\end{code}

\noindent As before, LiquidHaskell checks the above by
[automatically instantiating refinements](#foldlinst)
for the type parameters of `foldl'`, saving us a fair
bit of typing and enabling the use of the elegant
polymorphic, higher-order combinators we know and love.

\exercise **Sanitization** Invariants are all well
and good for data computed *inside* our programs.
The only way to ensure the legality of data coming
from *outside*, i.e. from the "real world", is to
writing a sanitizer that will check the appropriate
invariants before constructing a `Sparse` vector.
Write the specification and implementation of a
sanitizer `fromList`, such that the following
code typechecks:

\begin{code}
fromList          :: Int   -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = undefined   

{-@ test1         :: SparseN String 3 @-}
test1             = fromJust $ fromList  3 [(0, "cat"), (2, "mouse")]
\end{code}


\exercise **Summation** Write the specification and implementation
of a function `add` that performs the addition of two `Sparse`
vectors of the *same* dimension, yielding an output of that dimension.
When you are done, the following code should typecheck:

\begin{code}
add     :: (Num a) => Sparse a -> Sparse a -> Sparse a
add x y = undefined 

{-@ test2 :: SparseN Int 3 @-}   
test2    = add vec1 vec2 
  where 
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]
\end{code}

Ordered Lists
--------------

As a second example of refined data types, lets consider a
different problem: representing *ordered* sequences. Here's
a type for sequences that mimics the classical list:

\begin{code}
data IncList a = Emp
               | (:<) { hd :: a, tl :: IncList a }   

infixr 9 :<
\end{code}

\noindent 
The Haskell type above does not state that the elements
be in order of course, but we can specify that requirement
by refining *every* element in `tl` to be *greater than* `hd`: 

\begin{code}
{-@ data IncList a = Emp
                   | (:<) { hd :: a, tl :: IncList {v:a | hd < v} }
  @-}
\end{code}

\newthought{Refined Data Constructors} Once again,
the refined data definition is internally converted
into a "smart" refined data constructor

\begin{spec}
-- Generated Internal representation
data IncList a where
  Emp  :: IncList a
  (:<) :: hd:a -> tl:IncList {v:a | hd < v} -> IncList a
\end{spec}

\noindent which ensures that we can only create legal, i.e. ordered lists.

\begin{code}
okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH
\end{code}

**HEREHEREHERE**


Its all very well to *specify* lists with various kinds of invariants. 
The question is, how easy is it to *establish* these invariants?

Lets find out, by turning inevitably to that staple of all forms of
formal verification: your usual textbook sorting procedures.

**Insertion Sort**

First up: insertion sort. Well, no surprises here:

\begin{code}
{-@ insertSort    :: (Ord a) => xs:[a] -> (IncrList a) @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs) 
\end{code}

The hard work is done by `insert` which places an 
element into the correct position of a sorted list

\begin{code}
insert y []     = [y]
insert y (x:xs) 
  | y <= x      = y : x : xs 
  | otherwise   = x : insert y xs
\end{code}

LiquidHaskell infers that if you give `insert` an element 
and a sorted list, it returns a sorted list.

\begin{code}
{-@ insert :: (Ord a) => a -> IncrList a -> IncrList a @-}
\end{code}

If you prefer the more Haskelly way of writing insertion sort, 
i.e. with a `foldr`, that works too. Can you figure out why?

\begin{code}
{-@ insertSort' :: (Ord a) => [a] -> IncrList a @-}
insertSort' xs  = foldr insert [] xs
\end{code}

**Merge Sort**

Well, you know the song goes. First, we write a function 
that **splits** the input into two parts:

\begin{code}
split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys) 
  where 
    (xs, ys)   = split zs
split xs       = (xs, [])
\end{code}

Then we need a function that **merges** two (sorted) lists

\begin{code}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys) 
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys
\end{code}

LiquidHaskell deduces that if both inputs are 
ordered, then so is the output.

\begin{code}
{-@ merge :: (Ord a) => IncrList a 
                     -> IncrList a 
                     -> IncrList a 
  @-}
\end{code}

Finally, using the above functions we write `mergeSort`:

\begin{code}
{-@ mergeSort :: (Ord a) => [a] -> IncrList a @-}
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs) 
  where 
    (ys, zs)  = split xs
\end{code}

Lets see how LiquidHaskell proves the output type. 

+ The first two cases are trivial: for an empty 
  or singleton list, we can vacuously instantiate 
  the abstract refinement with *any* concrete 
  refinement.

+ For the last case, we can inductively assume 
 `mergeSort ys` and `mergeSort zs` are sorted 
  lists, after which the type inferred for 
  `merge` kicks in, allowing LiquidHaskell to conclude
  that the output is also sorted.

**Quick Sort**

The previous two were remarkable because they were, well, quite *unremarkable*. 
Pretty much the standard textbook implementations work *as is*. 
Unlike the [classical][omega-sort] [developments][hasochism] 
using indexed types we don't have to define any auxiliary 
types for increasing lists, or lists whose value is in a 
particular range, or any specialized `cons` operators and 
so on.

With *quick sort* we need to do a tiny bit of work.

\begin{code} We would like to define `quickSort` as
{-@ quickSort'    :: (Ord a) => [a] -> IncrList a @-}
quickSort' []     = []
quickSort' (x:xs) = lts ++ (x : gts) 
  where 
    lts           = quickSort' [y | y <- xs, y < x]
    gts           = quickSort' [z | z <- xs, z >= x]
\end{code}

But, if you try it out, you'll see that LiquidHaskell 
*does not approve*. What could possibly be the trouble?

The problem lies with *append*. What type do we give `++`? 

\begin{code} We might try something like
(++) :: IncrList a -> IncrList a -> IncrList a
\end{code}

\begin{code} but of course, this is bogus, as 
[1,2,4] ++ [3,5,6]
\end{code}

is decidedly not an `IncrList`!

Instead, at this particular use of `++`, there is
an extra nugget of information: there is a *pivot*
element `x` such that every element in the first 
argument is less than `x` and every element in 
the second argument is greater than `x`. 

There is no way we can give the usual append `++` 
a type that reflects the above as there is no pivot 
`x` to refer to. Thus, with a heavy heart, we must
write a specialized pivot-append that uses this fact:

\begin{code}
pivApp piv []     ys  = piv : ys
pivApp piv (x:xs) ys  = x   : pivApp piv xs ys
\end{code}

Now, LiquidHaskell infers that 

\begin{code}
{-@ pivApp :: piv:a 
           -> IncrList {v:a | v <  piv} 
           -> IncrList {v:a | v >= piv} 
           -> IncrList a 
  @-}
\end{code}

And we can use `pivApp` to define `quickSort' simply as:

\begin{code}
{-@ quickSort    :: (Ord a) => [a] -> IncrList a @-}
quickSort []     = []
quickSort (x:xs) = pivApp x lts gts 
  where 
    lts          = quickSort [y | y <- xs, y < x ]
    gts          = quickSort [z | z <- xs, z >= x]
\end{code}



Ordered Trees
------------- 



