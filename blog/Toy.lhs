Parametric Invariants via Abstract Refinements
==============================================

Lets see how abstract refinements can be used to express parametric
invariants over base types and types with type class constrains.

\begin{code}
module Toy where

import Language.Haskell.Liquid.Prelude (isEven)
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

And write a function `maxEvens`.
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

Parametric Invariants over Class-Predicated Type Variables
----------------------------------------------------------

The example above regularly arises in practice, due to type classes. 
\begin{code}In Haskell, the functions above are typed
(<=)    :: (Ord a) => a -> a -> Bool
max     :: (Ord a) => a -> a -> a
maximum :: (Ord a) => [a] -> a
\end{code}

We might be tempted to simply ignore the type class constraint, 
and just treat `maximum` as `[a] -> a` but, of course, 
this would be quite unsound, as typeclass predicates trivially preclude
universal quantification over refinement types. 
Consider the function `sum :: (Num a) => [a] -> a` which adds the elements 
of a list.

The `Num` class constraint implies that numeric operations occur 
in the function, so
if we pass `sum` a list of odd numbers, 
we are _not_ guaranteed to get back an odd number. 

Thus, how do we soundly verify the desired type of `maxEvens`
without instantiating class predicated type parameters with 
arbitrary refinement types? First, via the same analysis as 
the monomorphic `Int` case, we establish that

\begin{code}
{-@ maxPoly :: forall <p :: a -> Bool>. d:(Ord a) => x:a<p> -> y:a<p> -> a<p> @-}
maxPoly     :: (Ord a) => a -> a -> a 
maxPoly x y = if x <= y then y else x

{-@ maximumPoly :: forall <p :: a -> Bool>. d:(Ord a) => x:[a<p>] -> a<p> @-}
maximumPoly :: (Ord a) => [a] -> a
maximumPoly (x:xs) = foldr maxPoly x xs
\end{code}


We can define `maxEvens2` that uses the above functions:

\begin{code}
{-@ maxEvens2 :: xs:[Int] -> {v:Int | v mod 2 = 0 } @-}
maxEvens2 xs = maximumPoly (0 : xs') 
  where xs' = [ x | x <- xs, isEven x]
\end{code}


Finally, at the call-site for `maximumPoly` in `maxEvens2` we
instantiate the type variable `a` with `Int`, and 
the abstract refinement `p` with `{\v -> v % 2 = 0}`
after which, the verification proceeds as described
earlier (for the `Int` case).
Thus, abstract refinements allow us to quantify over 
invariants without relying on parametric polymorphism, 
even in the presence of type classes.



