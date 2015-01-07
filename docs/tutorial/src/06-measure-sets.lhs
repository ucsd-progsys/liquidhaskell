

Elemental Measures {#setmeasure}
================


\begin{comment}
\begin{code}
module Sets where
import Data.Set hiding (filter, split)
import Prelude  hiding (reverse, filter)

main :: IO ()
main = return ()
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
  of tracked resources, and so on.

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

\noindent
is a valid formula, i.e. holds for all $x$, the solver "knows" that:

$$x = \tsng{1} \Rightarrow y = \tsng{2} \Rightarrow x = \tcap{x}{\tcup{y}{x}}$$

This is because, the above formulas belong to a decidable Theory of Sets
which can be reduced to McCarthy's more general [Theory of Arrays][mccarthy]. 
\footnotetext{See [this recent paper][z3cal] if you want to learn more about
how modern SMT solvers prove equalities like the above.}


Permutations
------------

Well-Scopedness 
---------------

Uniqueness
----------
