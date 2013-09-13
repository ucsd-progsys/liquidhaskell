-- ---
-- layout: post
-- title: "Parametric Invariants via Abstract Refinements"
-- date: 2013-01-10 16:12
-- comments: true
-- external-url:
-- categories: abstract refinements
-- author: Niki Vazou
-- published: false
-- ---

-- Lets see how *abstract refinements* can be used to express *parametric invariants*
-- over base types and *typeclasses*.


module Toy where

import Language.Haskell.Liquid.Prelude (isEven)


-- Parametric Invariants over Base Types
-- -------------------------------------

-- Suppose we have a monomorphic `max` function on `Int` values:

maxInt     :: Int -> Int -> Int
maxInt x y = if x <= y then y else x


-- \begin{code}`maxInt` could take many refinement types, for example
-- maxInt :: x:{v:Int | v > 0} -> y:{v:Int | v > 0} -> {v:Int | v > 0}
-- \end{code}

-- \begin{code}or
-- maxInt :: x:{v:Int | v < 10} -> y:{v:Int | v < 10} -> {v:Int | v < 10}
-- \end{code}

-- \begin{code}or even
-- maxInt :: x:{v:Int | prime{v)} -> y:{v:Int | prime(v)} -> {v:Int | prime(v)}
-- \end{code}

-- We can prove that if a property holds for both  `x` and `y`, then it also holds for `maxInt x y`.
-- So, we would like to _abstract_ over the refinements that both arguments and the result have.
-- We can acchieve this with with _abstract refinements_, which let us quantify or parameterize a type over its constituent refinements.  For example, we can type `maxInt` as

{-@ maxInt :: forall <p :: Int -> Prop>. x:Int <p> -> y:Int <p> -> Int <p>@-}


-- where `Int<p>` is an abbreviation for the refinement type `{v:Int | p(v)}`.
-- Intuitively, an abstract refinement `p` is encoded in the refinement logic
-- as an _uninterpreted function symbol_, which satisfies the
-- _congruence axiom_

-- ~~~
-- forall X, Y. X = Y => P(X) = P(Y)
-- ~~~

-- Thus, it is trivial to verify, with an SMT solver, that `maxInt`
-- enjoys the above type: the input types ensure that both `p(x)` and `p(y)`
-- hold and hence the returned value in either branch satisfies
-- the refinement  `{v:Int | p(v)}`, thereby ensuring the output
-- type.

-- By the same reasoning, we can define the `maximumInt` operator on lists:

{-@ maximumInt :: forall <p :: Int -> Prop>. x:{v:[Int <p>]|((len v)>0)} -> Int <p>@-}
maximumInt ::  [Int] -> Int
maximumInt (x:xs) = foldr maxInt x xs


-- \begin{code}Now, we can use the function `isEven` from Language.Haskell.Liquid.Prelude library:
-- {- assume isEven :: x:Int -> {v:Bool | (Prop(v) <=> ((x mod 2) = 0))} -}
-- isEven   :: Int -> Bool
-- isEven x = x `mod` 2 == 0
-- \end{code}

-- And write a function `maxEvens`.

maxEvens1 xs = maximumInt xs''
  where xs'  = [ x | x <- xs, isEven x]
        xs'' = 0 : xs'


-- Since `(0:xs')` is a list if values with type
-- `{v:Int | (x mod 2) = 0}`,
-- we can instantiate
-- the _refinement_ parameter of `maximumInt` with the concrete
-- refinement
-- `{\v -> v mod 2) = 0}`,
-- after which type of `maxEvens1` can be proved to be:


{-@ maxEvens1 :: xs:[Int] -> {v:Int | v mod 2 = 0 } @-}


-- Parametric Invariants over Class-Predicated Type Variables
-- ----------------------------------------------------------

-- The example above regularly arises in practice, due to type classes.
-- \begin{code}In Haskell, the functions above are typed
-- (<=)    :: (Ord a) => a -> a -> Bool
-- max     :: (Ord a) => a -> a -> a
-- maximum :: (Ord a) => [a] -> a
-- \end{code}

-- We might be tempted to simply ignore the type class constraint,
-- and just treat `maximum` as `[a] -> a` but, of course,
-- this would be quite unsound, as typeclass predicates trivially preclude
-- universal quantification over refinement types.
-- Consider the function `sum :: (Num a) => [a] -> a` which adds the elements
-- of a list.

-- The `Num` class constraint implies that numeric operations occur
-- in the function, so
-- if we pass `sum` a list of odd numbers,
-- we are _not_ guaranteed to get back an odd number.

-- Thus, how do we soundly verify the desired type of `maxEvens`
-- without instantiating class predicated type parameters with
-- arbitrary refinement types? First, via the same analysis as
-- the monomorphic `Int` case, we establish that


{-@ maxPoly :: forall <p :: a -> Prop>. (Ord a) => x:a<p> -> y:a<p> -> a<p> @-}
maxPoly     :: (Ord a) => a -> a -> a
maxPoly x y = if x <= y then y else x

{-@ maximumPoly :: forall <p :: a -> Prop>. (Ord a) => x:{v:[a<p>]|((len v)>0)} -> a<p> @-}
maximumPoly :: (Ord a) => [a] -> a
maximumPoly (x:xs) = foldr maxPoly x xs



-- We can define `maxEvens2` that uses the above functions:


{-@ maxEvens2 :: xs:[Int] -> {v:Int | v mod 2 = 0 } @-}
maxEvens2 xs = maximumPoly xs''
  where xs'  = [ x | x <- xs, isEven x]
        xs'' = 0 :xs'



-- Finally, at the call-site for `maximumPoly` in `maxEvens2` we
-- instantiate the type variable `a` with `Int`, and
-- the abstract refinement `p` with `{\v -> v % 2 = 0}`
-- after which, the verification proceeds as described
-- earlier (for the `Int` case).
-- Thus, abstract refinements allow us to quantify over
-- invariants without relying on parametric polymorphism,
-- even in the presence of type classes.
