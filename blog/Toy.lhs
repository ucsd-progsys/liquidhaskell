Parametric Invariants via Abstract Refinements
==============================================

Lets see how abstract refinements can be used to express parametric
invariants over base types and types with type class constrains.

\begin{code}
module Toy where

import Language.Haskell.Liquid.Prelude (isEven, isOdd)
\end{code}

Parametric Invariants over Base Types
-------------------------------------

Suppose we have a monomorphic `max` function on `Int` values:
\begin{code}
maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 
\end{code}

We can see that if a property holds for both  `x` and `y`, 
then it also holds for `maxInt x y` and we would like to express this
fact in the type of `maxInt`.
We can acchieve this with 
with _abstract refinements_, which let us 
quantify or parameterize a type over its constituent refinements.
For example, we can type `maxInt` as
\begin{code}
{-@ maxInt :: forall <p :: Int -> Bool>. x:Int <p> -> y:Int <p> -> Int <p>@-}
\end{code}

where `Int<p>` is an abbreviation for the refinement type `{v:Int | p(v)}`.
Intuitively, an abstract refinement `p` is encoded in the refinement logic 
as an _uninterpreted function symbol_, which satisfies the
_congruence axiom_

~~~
forall X, Y. X = Y => P(X) = P(Y)
~~~

Thus, it is trivial to verify, with an SMT solver, that `maxInt` 
enjoys the above type: the input types ensure that both `p(x)` and `p(y)` 
hold and hence the returned value in either branch satisfies 
the refinement  `{v:Int | p(v)}`, thereby ensuring the output 
type. 

By the same reasoning, we can define the `maximumInt` operator on lists:
\begin{code}
{-@ maximumInt :: forall <p :: Int -> Bool>. x:[Int <p>] -> Int <p>@-}
maximumInt ::  [Int] -> Int 
maximumInt (x:xs) = foldr maxInt x xs
\end{code}

\begin{code}Now, we can use the function `isEven` from Language.Haskell.Liquid.Prelude library:
{- assume isEven :: x:Int -> {v:Bool | ((? v) <=> ((x mod 2) = 0))} -}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0
\end{code}

And write a function @maxEvens@.
\begin{code}
maxEvens1 xs = maximumInt (0 : xs') 
  where xs' = [ x | x <- xs, isEven x]
\end{code}

Since `(0:xs')` is a list if values with type 
`{v:Int | (x mod 2) = 0}`, 
we can instantiate
the _refinement_ parameter of `maximumInt` with the concrete 
refinement 
`{\v -> v mod 2) = 0}`,
after which type of `maxEvens1` can be proved to be:

\begin{code}
{-@ maxEvens1 :: xs:[Int] -> {v:Int | v mod 2 = 0 } @-}
\end{code}

With exactly the same reasoning, we can write the following `maxOdd1` function:
\begin{code}
{-@ maxOdds1 :: xs:[Int] -> {v:Int | v mod 2 = 1 } @-}
maxOdds1 xs = maximumInt (1 : xs') 
  where xs' = [ x | x <- xs, isOdd x]
\end{code}
