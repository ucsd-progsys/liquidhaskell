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
       , dotProd, dotProd', plus, fromList  

         -- * Sparse: Examples
       , okSP, badSP, test1, test2
 
          -- * OrdList: Data
       , IncList  (..)

          -- * OrdList: Examples
       , okList, badList 

          -- * OrdList: Functions
       ,  insertSort, insertSort', mergeSort, quickSort

          -- * BST: Data
       , BST (..)

          -- * BST: Functions 
       , mem, add, delMin, del, bstSort, toBST, toIncList

          -- * BST: Examples
       , okBST, badBST 
                                              
       )
      where

import Prelude      hiding (abs, length, min)
import Data.List    (foldl')
import Data.Vector  hiding (singleton, foldl', foldr, fromList) 
import Data.Maybe   (fromJust)

dotProd, dotProd' :: Vector Int -> Sparse Int -> Int
test1 :: Sparse String
test2 :: Sparse Int

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
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
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ] 
\end{code}

\noindent but rejects, due to the invalid index:

\begin{code}
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]
\end{code}

\newthought{Field Measures} It is convenient to write an alias
for sparse vectors of a given size `N`. We can use the field name
`spDim` as a *measure*, like `vlen`. That is, we can use `spDim`
inside refinements:

\begin{code}
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-} 
\end{code}

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
[automatically instantiating refinements](#sparsetype)
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


\exercise Write the specification and implementation
of a function `plus` that performs the addition of two `Sparse`
vectors of the *same* dimension, yielding an output of that dimension.
When you are done, the following code should typecheck:

\begin{code}
plus     :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus x y = undefined 

{-@ test2 :: SparseN Int 3 @-}   
test2    = plus vec1 vec2 
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
                   | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} }
  @-}
\end{code}

\newthought{Refined Data Constructors} Once again,
the refined data definition is internally converted
into a "smart" refined data constructor

\begin{spec}
-- Generated Internal representation
data IncList a where
  Emp  :: IncList a
  (:<) :: hd:a -> tl:IncList {v:a | hd <= v} -> IncList a
\end{spec}

\noindent which ensures that we can only create legal ordered lists.

\begin{code}
okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH
\end{code}

\noindent 
Its all very well to *specify* ordered lists.
Next, lets see how its equally easy to *establish*
these invariants by implementing several textbook
sorting routines.

\newthought{Insertion Sort} 
First, lets implement insertion sort, which converts an ordinary
list `[a]` into an ordered list `IncList a`.

\begin{code}
insertSort        :: (Ord a) => [a] -> IncList a 
insertSort []     = Emp 
insertSort (x:xs) = insert x (insertSort xs) 
\end{code}

The hard work is done by `insert` which places an element into
the correct position of a sorted list. LiquidHaskell infers that
if you give `insert` an element and a sorted list, it returns a
sorted list.

\begin{code}
insert             :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs) 
  | y <= x         = y :< x :< xs 
  | otherwise      = x :< insert y xs
\end{code}

\exercise Complete the implementation of the function below to
use `foldr` to eliminate the explicit recursion in `insertSort`.

\begin{code}
insertSort'     :: (Ord a) => [a] -> IncList a
insertSort' xs  = foldr f b xs
  where
     f          = undefined    -- Fill this in
     b          = undefined    -- Fill this in
\end{code}

\newthought{Merge Sort} Similarly, it is easy to write merge sort,
by implementing the three steps. First, we write a function that
*splits* the input into two equal sized halves:

\begin{code}
split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys) 
  where 
    (xs, ys)   = split zs
split xs       = (xs, [])
\end{code}

\noindent 
Second, we need a function that *combines* two ordered lists

\begin{code}
merge                    :: (Ord a) => IncList a -> IncList a -> IncList a 
merge xs  Emp            = xs
merge Emp ys             = ys
merge (x:< xs) (y :< ys) 
  | x <= y               = x :< merge xs (y :< ys)
  | otherwise            = y :< merge (x :< xs) ys
\end{code}

\noindent 
Finally, we compose the above steps to divide (i.e. `split`)
and conquer (`sort` and `merge`) the input list:

\begin{code}
{-@ mergeSort :: (Ord a) => [a] -> IncList a @-}
mergeSort []  = Emp  
mergeSort [x] = x :< Emp
mergeSort xs  = merge (mergeSort ys) (mergeSort zs) 
  where 
    (ys, zs)  = split xs
\end{code}

\exercise Why is the following implementation of `quickSort`
rejected by LiquidHaskell? Modify it so it is accepted.

\begin{code}
quickSort           :: (Ord a) => [a] -> IncList a
quickSort []        = Emp 
quickSort (x:xs)    = append lessers greaters 
  where 
    lessers         = quickSort [y | y <- xs, y < x ]
    greaters        = quickSort [z | z <- xs, z >= x]

append              :: (Ord a) => IncList a -> IncList a -> IncList a
append Emp       ys = ys
append (x :< xs) ys = x :< append xs ys 
\end{code}

Ordered Trees
------------- 

As a last example of refined data types, let us consider binary search ordered
trees, defined thus:

\begin{code}
data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }
\end{code}

\newthought{Binary Search Trees}
enjoy the [property](http://en.wikipedia.org/wiki/Binary_search_tree)
that each `root` lies (strictly) between the elements belonging in the
`left` and `right` subtrees hanging off the the root. The ordering
invariant makes it easy to check whether a certain value occurs in the
tree.  If the tree is empty i.e. a Leaf, then the value does not occur
in the tree.  If the given value is at the root then the value does
occur in the tree.  If it is less than (respectively greater than) the
root, we recursively check whether the value occurs in the left
(respectively right) subtree.


\begin{marginfigure}
\includegraphics[height=2.0in]{img/bst.png}
\caption{A Binary Search Tree with values between 1 and 9.
         Each root's value lies between the values appearing
         in its left and right subtrees.}
\label{fig:bst}
\end{marginfigure}


Figure \ref{fig:bst} shows a binary search tree whose nodes
are labeled with a subset of values from `1` to `9`.
We might represent such a tree with the Haskell value:

\begin{code}
okBST :: BST Int
okBST =  Node 6 
             (Node 2
                 (Node 1 Leaf Leaf)
                 (Node 4 Leaf Leaf))
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)
\end{code}

\newthought{Refined Data Type} The Haskell type says nothing about the
ordering invariant, and hence, cannot prevent us from creating illegal
`BST` values that violate the invariant. We can remedy this with a
refined data definition that captures the invariant:

\begin{code}
{-@ data BST a = Leaf
               | Node { root  :: a
                      , left  :: BST {v:a | v < root}
                      , right :: BST {v:a | root < v} }
  @-}
\end{code}


\newthought{Refined Data Constructors} As before, the above data definition
creates a refined "smart" constructor for `BST`

\begin{spec}
data BST a where
  Leaf :: BST a
  Node :: r:a -> BST {v:a | v < r} -> BST {v:a | r < v} -> BST a
\end{spec}

\noindent which *prevents* us from creating illegal trees

\begin{code}
badBST :: BST Int
badBST =  Node 6 
             (Node 4
                 (Node 1 Leaf Leaf)
                 (Node 2 Leaf Leaf))    -- Out of order, rejected by LH 
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)
\end{code}

\exercise Can a `BST Int` contain duplicates?

\newthought{Membership}
Lets write some functions to create and manipulate
these trees. First, a function to check whether a value
is in a `BST`:

\begin{code}
mem                 :: (Ord a) => a -> BST a -> Bool
mem _ Leaf          = False
mem k (Node k' l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r 
\end{code}

\newthought{Singleton} Next, another easy warm-up: a function to create
a `BST` with a single given element:

\begin{code}
one   :: a -> BST a
one x = Node x Leaf Leaf
\end{code}

\newthought{Insertion} Next, lets write a function that adds an
element to a `BST`.
\footnotetext{Amusingly, while typing out the below I swapped the
`k` and `k'` which caused LiquidHaskell to complain.}

\begin{code}
add                  :: (Ord a) => a -> BST a -> BST a
add k' Leaf          = one k'
add k' t@(Node k l r)
  | k' < k           = Node k (add k' l) r
  | k  < k'          = Node k l (add k' r)
  | otherwise        = t 
\end{code}

\newthought{Minimum} Next, lets write a function to delete the *minimum*
element from a `BST`. This function will return a *pair* of outputs --
the smallest element and the remainder of the tree. We can say that the
output element is indeed the smallest, by saying that the remainder's
elements exceed the element. To this end, lets define a helper type:
\footnotetext{This helper type approach is rather verbose. We should be able
to just use plain old pairs and specify the above requirement as a
*dependency* between the pairs' elements. Later, we will see how to
do so using [abstract refinements](http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf).}

\begin{code}
data MinPair a = MP { minElt :: a, rest :: BST a }
\end{code}

\noindent We can specify that `minElt` is indeed smaller than all
the elements in `rest` via the data type refinement:

\begin{code}
{-@ data MinPair a = MP { minElt :: a, rest :: BST {v:a | minElt < v} } @-}
\end{code}

\noindent Finally, we can write the code to compute `MinPair`

\begin{code}
delMin                 :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
  where
    MP k' l'           = delMin l 
delMin Leaf            = die "Don't say I didn't say I didn't warn ya!"
\end{code}

\exercise Use `delMin` to complete the implementation
of `del` which *deletes* a given element from a `BST`,
if it is present.

\begin{code}
del                   :: (Ord a) => a -> BST a -> BST a
del k' t@(Node k l r) = undefined
del _  t              = t
\end{code}

\exercise The function `delMin` is only sensible for non-empty trees.
[Read ahead](#usingmeasures) to learn how to specify and verify that
it is only called with such trees, and then apply that technique here
to verify the call to `die` in `delMin`.

\exercise Complete the implementation of `toIncList` to obtain a `BST`
based sorting routine `bstSort`.

\begin{code}
bstSort   :: (Ord a) => [a] -> IncList a
bstSort   = toIncList . toBST

toBST     :: (Ord a) => [a] -> BST a
toBST     = foldr add Leaf  

toIncList :: BST a -> IncList a
toIncList = undefined
\end{code}

\hint This exercise will be a lot easier after you finish the
`quickSort` exercise. Note that the signature for `toIncList`
does not use `Ord` and so you cannot use a sorting procedure
to implement it.


Recap
-----

In this chapter we saw how LiquidHaskell lets you refine data
type definitions to capture sophisticated invariants. These
definitions are internally represented by refining the types
of the data constructors, automatically making them "smart"  in
that they preclude the creation of illegal values that violate
the invariants. We will see much more of this handy technique
in future chapters.

One recurring theme in this chapter was that we had to create new
versions of standard datatypes, just in order to specify certain
invariants.  For example, we had to write a special list type, with
its own *copies* of nil and cons. Similarly, to implement `delMin` we
had to create our own pair type.

\newthought{This duplication} of types is quite tedious.
There should be a way to just slap the desired invariants
on to *existing* types, thereby facilitating their reuse.
In a few chapters, we will see how to achieve this reuse
by *abstracting refinements* from the definitions of
datatypes or functions in the same way we abstract
the element type `a` from containers like `[a]` or `BST a`.   




