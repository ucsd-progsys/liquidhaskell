

Elemental Measures {#setmeasure}
================


\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

module Sets where
import Data.Set hiding (insert, partition, filter, split, elems)
import Prelude  hiding (elem, reverse, filter)

main :: IO ()
main = return ()

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

isUnique, isNotUnique :: [Int]
mergeSort :: (Ord a) => [a] -> [a]
range :: Int -> Int -> [Int]

-- TODO: qualifier needed for focus* ? not clear. Eric: can you check?
{- q0 :: x:a ->  {v:[a] | not (Elem x v)} @-}
q0   :: a -> [a]
q0 _ = []
\end{code}
\end{comment}

Often, correctness requires us to reason about the *set of elements*
represented inside a data structure, or manipulated by a function.

\newthought{Sets} appear everywhere. For example, we'd like to know that:

+ *sorting* routines return permutations of their inputs --
  i.e. return collections whose elements are the same as the
  input' set,

+ *resource management* functions do not inadvertently
  create duplicate elements or drop  elements from set
  of tracked resources.

+ *syntax-tree* manipulating procedures create well-scoped
  trees where (the set of) used variables are (contained
  within the set of variables) previously defined.

\newthought{SMT Solvers} support rather expressive logics. In addition to the
linear arithmetic and uninterpreted functions, they can [efficiently decide](smt-set)
formulas over sets. Next, lets see how LiquidHaskell lets us exploit this fact
to develop types and interfaces that guarantee invariants over the (set of)
elements of a structures.

Talking about Sets
------------------

First, we need a way to talk about sets in the refinement logic. We could
roll our own special Haskell type \footnotetext{See [this](blog-set) for a brief
description of how to do so}, but for now, lets just use the `Set a`
type from the prelude's `Data.Set`.

\newthought{Lifted Operators} The LiquidHaskell prelude *lifts* the basic set
operators from `Data.Set` into the refinement logic, i.e. defines the following
logical functions that correspond to the Haskell functions of the same name:

\begin{spec}
measure empty        :: Set a
measure singleton    :: a -> Set a
measure member       :: a -> Set a -> Bool  
measure union        :: Set a -> Set a -> Set a
measure intersection :: Set a -> Set a -> Set a
measure difference   :: Set a -> Set a -> Set a
\end{spec}

\newthought{Interpreted Operators}
The above operators are *interpreted* by the SMT solver.
That is, just like the SMT solver "knows", via the
axioms of the theory of arithmetic that:
$$x = 2 + 2 \Rightarrow x = 4$$
is a valid formula, i.e. holds for all $x$, the solver "knows" that:
$$x = \tsng{1} \Rightarrow y = \tsng{2} \Rightarrow x = \tcap{x}{\tcup{y}{x}}$$
This is because, the above formulas belong to a decidable Theory of Sets
reduces to McCarthy's more general [Theory of Arrays][mccarthy]. 
\footnotetext{See [this recent paper][z3cal] to learn how modern SMT solvers prove equalities like the above.}


Proving QuickCheck Style Properties {#quickcheck} 
-----------------------------------

To get the hang of whats going on, lets do a few warmup exercises,
using LiquidHaskell to prove various simple "theorems" about sets
and operations over them.

\newthought{Refined Set API} To make it easy to write down theorems,
we've refined the types of the operators in `Data.Set` so that they
mirror their logical counterparts:

\begin{spec}
empty        :: {v:Set a | v = empty} 
singleton    :: x:a -> {v:Set a | v = singleton x} 
union        :: x:Set a -> y:Set a -> {v:Set a | v = union x y}
intersection :: x:Set a -> y:Set a -> {v:Set a | v = intersection x y}
difference   :: x:Set a -> y:Set a -> {v:Set a | v = difference x y}
member       :: x:a -> s:Set a -> {v:Bool | Prop v <=> member x s}  
\end{spec}

\newthought{Asserting Properties} Lets write our theorems
as [QuickCheck](quickcheck) style *properties*, that is,
as functions from arbitrary inputs to a `Bool` output
that must always be `True`. Lets define aliases for
the singletons `True` and `False`:

\begin{code}
{-@ type True  = {v:Bool |      Prop v } @-}
{-@ type False = {v:Bool | not (Prop v)} @-}
\end{code}

\noindent We can use `True` to state and prove theorems. For example,
something (boring) like the arithmetic equality above becomes:

\begin{code}
{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x   = (x == 1 + 1) `implies` (x == 2)
\end{code}

\noindent Where `implies` is just the implication function over ``Bool``

\begin{code}
{-@ implies        :: p:_ -> q:_ -> {v:Bool | Prop v <=> (Prop p => Prop q)} @-}
implies False _    = True
implies _     True = True 
implies _    _     = False
-- implies p q = not p || q
\end{code}

\exercisen{Bounded Addition} Write a QuickCheck style proof of the fact
that $x < 100 \wedge y < 100 \Rightarrow x + y < 200$.

\begin{code}
{-@ prop_x_y_200 :: _ -> _ -> True @-}
prop_x_y_200 x y = False -- fill in the appropriate body to obtain the theorem. 
\end{code}


\newthought{Intersection is Commutative} Ok, lets prove things about
sets and their operators! First, lets check that  `intersection` is
commutative:

\begin{code}
{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y 
  = (x `intersection` y) == (y `intersection` x)
\end{code}

\newthought{Union is Associative} Similarly, we might verify
that union is associative:

\begin{code}
{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_union_assoc x y z 
  = (x `union` (y `union` z)) == (x `union` y) `union` z
\end{code}

\newthought{Union Distributes over Intersection} and while we're at it,
check various distributivity laws of Boolean algebra:

\begin{code}
{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z 
  =  x `intersection` (y `union` z) == (x `intersection` y) `union` (x `intersection` z) 
\end{code}

\newthought{Non-Theorems}
Of course, while we're at it, let's make sure LiquidHaskell
doesn't prove anything that *isn't* true ...

\begin{code}
{-@ prop_cup_dif_bad :: _ -> _ -> True @-}
prop_cup_dif_bad x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = True  -- Fix this with a non-trivial precondition
\end{code}

\exercisen{Set Difference} Do you know why the above fails?
1. Use QuickCheck to find a *counterexample* for the property `prop_cup_dif_bad`, and,
2. Use the counterexample to assign `pre` a non-trivial (i.e. non `False`) condition
   so that the property can be proved.

Thus, LiquidHaskell's refined types offer a nice interface
for interacting with the SMT solvers in order to *prove*
theorems, while letting us use QuickCheck to generate
counterexamples.
\footnotetext{The [SBV][sbv] and [Leon][leon] projects
describes a different approach for using SMT solvers
from Haskell and Scala respectively, directly via an
embedded DSL.}

Content-Aware List API
----------------------

Our overall goal is to verify properties of programs.
Lets start off by refining the list API to precisely
track the list elements.

\newthought{Elements of a List} To specify the permutation
property, we need a way to talk about the set of elements
in a list. At this point, hopefully you know what we're
going to do: write a measure!

\begin{code}
{-@ measure elems @-}
elems        :: (Ord a) => [a] -> Set a
elems []     = empty
elems (x:xs) = singleton x `union` elems xs
\end{code}

\newthought{Strengthened Constructors}
Recall, that as before, the above definition automatically
strengthens the types for the constructors:

\begin{spec}
data [a] where
  []  :: {v:[a] | v = empty }
  (:) :: x:a -> xs:[a] -> {v:[a] | elems v = union (singleton x) (elems xs)}
\end{spec}

Next, to make the specifications concise, let's define a few predicate aliases:

\begin{code}
{-@ predicate EqElts  X Y   = elems X = elems Y                         @-}
{-@ predicate SubElts X Y   = Set_sub (elems X) (elems Y)               @-}
{-@ predicate DisjElts X Y  = Set_empty 0 = Set_cap (elems X) (elems Y) @-}
{-@ predicate Empty   X     = elems X = Set_empty 0                     @-}
{-@ predicate UnElts  X Y Z = elems X = Set_cup (elems Y) (elems Z)     @-}
{-@ predicate UnElt   X Y Z = elems X = Set_cup (Set_sng Y) (elems Z)   @-}
{-@ predicate Elem    X Y   = Set_mem X (elems Y)                       @-}
\end{code}


\newthought{Append}
First, here's good old `append`, but now with a specification that states
that the output indeed includes the elements from both the input lists.

\begin{code}
{-@ append'       :: xs:[a] -> ys:[a] -> {v:[a] | UnElts v xs ys} @-}
append' []     ys = ys
append' (x:xs) ys = x : append' xs ys
\end{code}

\exercisen{Reverse} Write down a type for `revHelper` so that `reverse'`
is verified by LiquidHaskell:

\begin{code}
{-@ reverse' :: xs:[a] -> {v:[a] | EqElts v xs} @-}
reverse' xs = revHelper [] xs

revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs
\end{code}

\exercisen{Partition} \singlestar Write down a
specification for `split` such that the subsequent
"theorem" `prop_partition_appent` is proved by LiquidHaskell.

\begin{code}
split            :: Int -> [a] -> ([a], [a])
split 0 xs       = ([], xs)
split n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = split (n-1) zs
split _ xs       = ([], xs)

{-@ prop_split_append  :: _ -> _ -> True @-}
prop_split_append n xs = elems xs == elems xs'
  where
    xs'      =  append' ys zs
    (ys, zs) =  split n xs 
\end{code}

\hint You may want to remind yourself about the
"dimension-aware" signature for `partition` from
[the earlier chapter](#listreducing).

\exercisen{Membership} Write down a signature for `elem`
that suffices to verify `test1` and `test2` by LiquidHaskell.

\begin{code}
{-@ elem      :: (Eq a) => a -> [a] -> Bool @-}
elem x (y:ys) = x == y || elem x ys
elem _ []     = False

{-@ test1 :: True @-}
test1      = elem 2 [1,2,3]

{-@ test2 :: False @-}
test2      = elem 2 [1,3] 
\end{code}

Permutations
------------

Next, lets use the refined list API to prove that
various list-sorting routines return *permutations*
of their inputs, that is, return output lists whose
elements are the *same as* those of the input lists.
Since we are focusing on the elements, lets not
distract ourselves with the ordering invariant
just, and reuse plain old lists.
\footnotetext{See [this](blog-ord-list) for how to
specify and verify order with plain old lists.}

\newthought{InsertionSort} is the simplest of all the
list sorting routines; we build up an (ordered) output
list `insert`ing each element of the input list into
the appropriate position of the output:

\begin{code}
insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys
\end{code}

\noindent Thus, the output of `insert` has all the
elements of the input `xs`, plus the new element `x`:

\begin{code}
{-@ insert :: x:a -> xs:[a] -> {v:[a] | UnElt v x xs } @-}
\end{code}

\noindent Which then lets us prove that the output of the sorting routine indeed
has the elements of the input:

\begin{code}
{-@ insertSort    :: (Ord a) => xs:[a] -> {v:[a] | EqElts v xs} @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)
\end{code}

\exercisen{Merge}
Write down a specification of `merge` such that the subsequent property is
verified by LiquidHaskell:

\begin{code}
{-@ merge :: xs:_ -> ys:_ -> {v:_ | UnElts v xs ys} @-}
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys
merge [] ys          = ys
merge xs []          = xs

{-@ prop_merge_app   :: _ -> _ -> True   @-}
prop_merge_app xs ys = elems zs == elems zs'
  where
    zs               = append' xs ys
    zs'              = merge   xs ys
\end{code}

\exercisen{MergeSort} \doublestar Once you write the correct type
for `merge` above, you should be able to prove the
surprising signature for `mergeSort` below.

\begin{code}
{-@ mergeSort :: (Ord a) => xs:[a] -> {v:[a] | Empty v} @-}
mergeSort []  = []
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = split mid xs
   mid        = length xs `div` 2
\end{code}

\noindent First, make sure you are able verify the given
signature. Next, obviously we don't want `mergeSort` to
return the empty list, so there's a bug somewhere in the
code. Find and fix it, so that you *cannot* prove that the
output is empty, but *can* prove that `EqElts v xs`.

Uniqueness
----------

Often, we want to enforce the invariant that a particular collection
contains *no duplicates*; as multiple copies in a collection of file
handles or system resources can create unpleasant leaks.
For example, the [XMonad](xmonad) window manager creates a
sophisticated *zipper* data structure to hold the list of
active user windows, and carefully maintains the invariant
that that there are no duplicates. Next, lets see how to specify
and verify this invariant using LiquidHaskell, first for lists, and
then for a simplified zipper.

\newthought{Specifying Uniqueness} How would we even describe the
fact that a list has no duplicates? There are in fact multiple
different ways, but the simplest is a *measure*:

\begin{code}
{-@ measure unique @-}
unique        :: (Ord a) => [a] -> Bool
unique []     = True
unique (x:xs) = unique xs && not (member x (elems xs)) 
\end{code}

\noindent We can define an alias for duplicate-free lists

\begin{code}
{-@ type UList a = {v:[a] | unique v }@-}
\end{code}

\noindent and then do a quick sanity check, that the
right lists are indeed `unique`

\begin{code}
{-@ isUnique    :: UList Int @-}
isUnique        = [1, 2, 3]        -- accepted by LH

{-@ isNotUnique :: UList Int @-}
isNotUnique     = [1, 2, 3, 1]     -- rejected by LH
\end{code}

\newthought{Filter}  Lets write some functions that preserve
`unique`ness. For example, `filter` returns a subset of its
elements. Hence, if the input was unique, the output is too:

\begin{code}
{-@ filter      :: _ -> xs:UList a -> {v: UList a | SubElts v xs} @-}
filter _ []     = []
filter f (x:xs)
  | f x         = x : xs' 
  | otherwise   = xs' 
  where
    xs'         = filter f xs
\end{code}

\exercisen{Reverse} \singlestar 
When we `reverse` their order, the set of elements is unchanged,
and hence unique (if the input was unique). Why does LiquidHaskell
reject the below? Can you fix things so that we can prove that the
output is a `UList a`?

\begin{code}
{-@ reverse     :: xs:UList a -> UList a    @-}
reverse         = go []
  where 
    {-@ go      :: acc:[a] -> xs:[a] -> [a] @-}
    go a []     = a
    go a (x:xs) = go (x:a) xs 
\end{code}

\newthought{Nub} One way to create a `unique` list is to start
with an ordinary list and throw away elements that we have `seen`
already.

\begin{code}
nub xs                = go [] xs 
  where
    go seen []        = seen
    go seen (x:xs)
      | x `isin` seen = go seen     xs
      | otherwise     = go (x:seen) xs
\end{code}

\noindent The key membership test is done by `isin`,
whose output is `True` exactly when the element is
in the given list. \footnotetext{Which should be
clear by now, if you did the exercise above \ldots}

\begin{code}
{-@ isin :: x:_ -> ys:_ -> {v:Bool | Prop v <=> Elem x ys }@-}
isin x (y:ys)
  | x == y    = True
  | otherwise = x `isin` ys
isin _ []     = False
\end{code}

\exercisen{Append} \singlestar Why does appending two
`UList`s not return a `UList`? Fix the type signature
below so that you can prove that the output is indeed
`unique`.

\begin{code}
{-@ append       :: UList a -> UList a -> UList a @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys
\end{code}

\exercisen{Range} \doublestar In the below `range i j`
returns the list of all `Int` between `i` and `j`.
Yet, LiquidHaskell refuses to acknowledge that the
output is indeed a `UList`. Modify the specification
and implementation, if needed, to obtain an equivalent
of `range` which *provably* returns a `UList Int`.

\begin{code}
{-@ type Btwn I J = {v:_ | I <= v && v < J} @-}
                   
{-@ range     :: i:Int -> j:Int -> UList (Btwn i j) @-}
range i j
  | i < j     = i : range (i + 1) j
  | otherwise = [] 
\end{code}

Unique Zippers
--------------

A [zipper](wiki-zipper) is an aggregate data stucture 
that is used to arbitrarily traverse the structure and
update its contents. For example, a zipper for a list is
a data type that contains an element (called `focus`)
that we are currently `focus`-ed on, a list of elements
to the `left` of (i.e. before) the focus, and a list of
elements to the `right` (i.e. after) the focus.


\begin{code}
data Zipper a = Zipper {
    focus  :: a      
  , left   :: [a]    
  , right  :: [a]
  }  
\end{code}

\newthought{XMonad} is a wonderful tiling window manager, that uses
a [zipper](xmonad-stackset) to store the set of windows being managed.
Xmonad requires the crucial invariant that the values in the zipper
be unique, i.e. have no duplicates.

\newthought{Refined Zipper}  
We can specify that all the values in the zipper are unique
by refining the `Zipper` data declaration to express that
both the lists in the structure are unique, disjoint,
and do not include `focus`.

\begin{code}
{-@ data Zipper a = Zipper {
      focus :: a
    , left  :: {v: UList a | not (Elem focus v)}
    , right :: {v: UList a | not (Elem focus v) && DisjElts v left }
    } @-}
\end{code}

\newthought{Constructing Zippers}
Our refined type makes *illegal states unrepresentable*;
by construction, we will ensure that every `Zipper` is
free of duplicates. Of course, it is straightforward to
create a valid `Zipper` from a `unique` list:

\begin{code}
{-@ differentiate    :: UList a -> Maybe (Zipper a) @-}
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs
\end{code}

\exercisen{Deconstructing Zippers} \singlestar
\noindent Dually, the elements of a unique zipper tumble out
into a unique list. Strengthen the types of `reverse` and `append`
above so that LiquidHaskell accepts the below signatures for `integrate`:

\begin{code}
{-@ integrate            :: Zipper a -> UList a @-}
integrate (Zipper x l r) = reverse l `append` (x : r)
\end{code}

\newthought{Shifting Focus} We can shift the focus element
left or right while preserving the invariants:

\begin{code}
focusLeft                      :: Zipper a -> Zipper a
focusLeft (Zipper t [] rs)     = Zipper x xs []     where (x:xs) = reverse (t:rs)
focusLeft (Zipper t (l:ls) rs) = Zipper l ls (t:rs)

focusRight                     :: Zipper a -> Zipper a
focusRight                     = reverseZipper . focusLeft . reverseZipper

reverseZipper                  :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls
\end{code}

\newthought{Filter} Finally, using the filter operation on lists
allows LiquidHaskell to prove that filtering a zipper 
also preserves uniqueness.
\begin{code}
filterZipper :: (a -> Bool) -> Zipper a -> Maybe (Zipper a)
filterZipper p (Zipper f ls rs) = case filter p (f:rs) of
    f':rs' -> Just $ Zipper f' (filter p ls) rs'      -- maybe move focus right 
    []     -> case filter p ls of                     -- filter back left
                    f':ls' -> Just $ Zipper f' ls' [] -- else left
                    []     -> Nothing
\end{code}

Recap
-----

In this chapter, we saw how SMT solvers can let us reason precisely about
the actual *contents* of data structures, via the theory of sets. We can

* Lift the set-theoretic primitives to (refined) Haskell functions from
  the `Data.Set` library,

* Use the functions to define measures like `elems` that characterize
  the contents of structures, and `unique` that describe high-level
  application specific properties.

* Use LiquidHaskell to then specify and verify that implementations
  enjoy various functional correctness properties, e.g. that sorting
  routines return permutations of their inputs, and various zipper
  operators preserve uniqueness.

Next, we present a variety of *case-studies* illustrating the techniques
so far on particular application domains.


