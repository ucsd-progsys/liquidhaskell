

Elemental Measures {#setmeasure}
================


\begin{comment}
\begin{code}
module Sets where
import Data.Set hiding (filter, split, elems)
import Prelude  hiding (elem, reverse, filter)

main :: IO ()
main = return ()

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

\end{code}
\end{comment}

Often, correctness requires us to reason about the *set of elements*
represented inside a data structure, or manipulated by a function.
For example, recall the following from the [introduction](#intro).

\begin{ghci}
ghci> :m +Data.Map 
ghci> let m = fromList [ ("haskell", "lazy")
                       , ("ocaml"  , "eager")]

ghci> m ! "haskell"
"lazy"

ghci> m ! "javascript"
"*** Exception: key is not in the map
\end{ghci}

\noindent
The problem illustrated above is quite a pervasive one; associative
maps pop up everywhere. Failed lookups are the equivalent of
`NullPointerDereference` exceptions in languages like Haskell.
It is rather difficult to use Haskell's type system to precisely
characterize the behavior of associative map APIs as ultimately,
this requires tracking the *dynamic set of keys* in the map.

\begin{figure}[h]
\includegraphics[height=1.0in]{img/piponi-tweet.png}
\caption{Wouldn't it be nice to know that a key was in a map?} 
\label{fig:piponi-tweet}
\end{figure}

\newthought{Sets} appear everywhere. The above is really the tip of the iceberg.
For example, we'd like to know that:

+ *sorting* routines return permutations of their inputs --
  i.e. return collections whose elements are the same as the
  input' set,

+ *syntax-tree* manipulating procedures create well-scoped
  trees where (the set of) used variables are (contained
  within the set of variables) previously defined.

+ *resource management* functions do not inadvertently
  create duplicate elements or drop  elements from set
  of tracked resources.

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
{-@ prop_x_y_200     :: _ -> _ -> True @-}
prop_x_y_200 x y = False -- fill in the appropriate body to obtain the theorem. 
\end{code}


\newthought{Intersection is Commutative} Ok, lets prove things about sets and their operators! First, lets check that  `intersection` is commutative:

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


Element-Aware List API
----------------------


Elements

Permutations
------------

While the above is a nice warm up exercise to understanding
how LiquidHaskell reasons about sets, our overall goal is
not to prove theorems about set operators, but instead to
specify and verify properties of programs. Lets start off
by refining the list API to precisely track the list elements.

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

Next, to make the specifications concise, let's define a few predicate aliases:

\begin{code}
{-@ type ListEq  a X  = {v:[a] | elems v = elems X}                    @-}
{-@ type ListSub a X  = {v:[a] | isSubsetOf (elems v) (elems X)}       @-}
{-@ type ListUn a X Y = {v:[a] | elems v = union (elems x) (elems y) } @-}
{-@ predicate EqElts  X Y      = elems X = elems Y                     @-}
{-@ predicate SubElts X Y      = isSubsetOf (elems X) (elems Y)        @-}
{-@ predicate UnionElts X Y Z  = elems X = Set_cup (elems Y) (elems Z) @-}
\end{code}

\newthought{Append}

\exercisen{Reverse}

\newthought{Filter}

\exercisen{Partition}

\exercisen{Membership}

\begin{code}
elem          :: (Eq a) => a -> [a] -> Bool
elem x (y:ys) = x == y || elem x ys
elem _ []     = False

{-@ test1 :: True @-}
test1      = elem 'a' "cat"

{-@ test2 :: False @-}
test2      = elem 'a' "dog" 
\end{code}

Permutations
------------

Next, lets use the refined list API to prove that
various list-sorting routines return *permutations*
of their inputs, that is, return output lists whose
elements are the *same as* those of the input lists.

isort
qsort

Well-Scopedness 
---------------

Uniqueness
----------
