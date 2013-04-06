Non termination
---------------

\begin{code}
module Lazy where

import Language.Haskell.Liquid.Prelude
\end{code}

Consinder a non-terminating function `f`:

\begin{code}
f :: a -> a
f x = if randomProp x then x else f x

randomProp :: a -> Bool
randomProp _ = False
\end{code}

If we call `f` with an arbitrary value `vv`, we will get
an infinite loop, so the result type of `f` does not have any
inhabitat and liquidHaskell can refine this type with `false`.
So, `f vv :: {v:a | false}`.

Consider now an environment, where `f vv` exists.
Since `false` exists in that environment, 
then any assertion can be prooved, so we can prove that `0==1`,
as follows:

\begin{code}
{-@ vv :: a @-}
vv :: a
vv = undefined

propNonTermination = liquidAssert ((\x _ -> x == 1) 0 foo)
  where foo = f vv
\end{code}


Infinite Data Structures
------------------------

Exactly the same applies for infinite data structures:

Consinder a function `list` that creates an infinite list:

\begin{code}
list :: a -> [a]
list x = if randomProp x then [] else x:list x
\end{code}

If we call `list` with an arbitrary value `vv`, we will get
an infinite list, so the result type of `list` does not have any
inhabitat and liquidHaskell can refine this type with `false`.
So, `list vv :: {v:[a] | false}`.

Consider now an environment, where `list vv` exists.
Since `false` exists in that environment, 
then any assertion can be prooved, so we can prove that `0==1`,
as follows:

\begin{code}
propInfiniteList = liquidAssert ((\x _ -> x == 1) 0 foo)
  where foo = list vv
\end{code}


Laziness
--------

Both these examples are unsound due to laziness.
In a call by value language the assetion
`(\x _ -> x == 1) 0 foo`
will never be evaluated, if `foo` does not terminate.
In a lazy language, the non-terminating expression `foo`
will just be ignored and the assertion `0==1` will be evaluated. 

A solution
----------

A solution to this problem is to ignore all the `false` predicates 
in the program.
So, if you run `liquid --nofalse foo.hs`
the constraints of the program will be solved in two steps.
In a first step the constrains will be solved 
to detect the `false` predicates.
In a second predicates the constrains will be solved, 
with all `false` predicates set to `true`.


There is one kind of constraints that should be modified in the second step

* `k_f, p_1, .. p_n <: k`, where `k_f:=false`
Since in the second step `k_f` is set to `true`.
Since `k` should not be constrainted to `true`, `k_f` should be removed from the left-hand-side of the constraint.
If also `n=0`, i.e., `k_f` is the only predicate in the left-hand-side, 
the constraint is removed at the second step.


TODO
----

\begin{code}
f' x = if randomProp x then x else f' x
propNonTerminationInt = liquidAssert ((\x _ -> x == 1) 0 foo)
  where foo  = f' 0
\end{code}

This breaks when the function is called with an `Integer`
because the type of the result is refined not with `false`, 
but with `(v = x, v > x, v < x)`. Why?
