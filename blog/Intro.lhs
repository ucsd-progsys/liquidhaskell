Refinement Types 101
====================

\begin{code}
module Intro where
\end{code}

One of the great things about Haskell, is its brainy type system that
allows us to enforce a variety of invariants at compile time, and hence
precluding a large swathe of errors at run time.

What is a Refinement Type?
--------------------------

In a nutshell, 

        Refinement Types = Types + Logical Predicates

That is, refinement types allow us to enrich types with *logical predicates* which
allow us to specify even more sophisticated properties. Say what? Let us jump right
in with a simple example, the number `0 :: Int`. 

As far as Haskell is concerned, the number is simply an `Int` (lets not worry about 
things like `Num` for the moment.) So are, `2` and `7` and `904`. However, we can 
dress up `zero` a little bit so that it stands apart. We might say:

\begin{code}
{-@ zero' :: {v: Int | 0 <= v} @-}
zero' :: Int
zero' = 0
\end{code}

Here, we have *refined* the basic type `Int` with a predicate.

\begin{code}In a nutshell, the refinement type
{v : Int | 0 <= v}
\end{code}

The binder `v` is called the *value variable*, and so the above denotes 
the set of `Int` values which are greater than `0`. Of course, we can
attach other predicates to the above value, for example

\begin{code}
{-@ zero''' :: {v: Int | 0 <= v && v < 100 } @-}
zero''' :: Int
zero''' = 0
\end{code}

which states that the number is in the range `0` to `100`, or

\begin{code}
{-@ zero''' :: {v: Int | v % 2 = 0} @-}
zero''' :: Int
zero''' = 0
\end{code}

where `%` is the *modulus* operator in the refinement logic, and hence,
where the type states that zero is an *even* number.

We can also *relate* these different definitions like so

\begin{code}
{-@ zero'''' :: {v: Int | v = zero } @-}
zero'''' :: Int
zero'''' = 0
\end{code}

The above type describes those values which are equal to the value bound to
the variable `zero`.

(Aside: we use a different names `zero'`, `zero''` etc. for a silly technical 
reason -- we want to ascribe a single type to a top-level name.)


Refining Function Types
-----------------------




