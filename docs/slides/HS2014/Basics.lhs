> {-@ LIQUID "--no-termination" @-}
> {-  LIQUID "-g-package-db" @-}
> {-  LIQUID "-g/Users/gridaphobe/.nix-profile/lib/ghc-7.8.3/package.conf.d/" @-}
> module Basics where
> 
> import Prelude hiding (head, max)
> import qualified Data.ByteString.Char8 as B
> import qualified Data.ByteString.Unsafe as B
> import Data.List (find)
> import Language.Haskell.Liquid.Prelude

Well-typed programs can't go wrong.

> dog = B.pack "dog"

< λ> B.unsafeIndex dog 2
< 103
< λ> B.unsafeIndex dog 10
< 0
< λ> B.unsafeIndex dog 10000000000
< segmentation fault

That's no good, it would be nice if the type system could prevent us from doing
that. Today I'm going to present our experience in designing such a type system,
and in using it to verify over 10KLoC of real Haskell code.


Refinement Types
================

We'll start with a lightning tour of LiquidHaskell before getting into the
gritty benchmarks.

A refinment type is a Haskell type where each component of the type is annotated
with a predicate from an SMT-decidable logic. For example,

< {v:Int | v >= 0 && v < 100}

describes the set of `Int`s that are between 0 and 100. We'll make heavy use of
*aliases* to simplify the types, e.g.

> {-@ predicate Btwn Lo N Hi = Lo <= N && N < Hi @-}
> {-@ type Rng Lo Hi = {v:Int | Btwn Lo v Hi}    @-}

< Rng 0 100

is equivalent to the first type.

We can describe a function's *contract* by refining its input and output types
with our desired pre- and post-conditions.

> {-@ range :: lo:Int -> hi:{Int | lo <= hi} -> {v:[Rng lo hi] | len v = hi - lo} @-}

This type tells us that `range` accepts two `Int`s, the second being larger than
the first, and returns a `[Int]` where all of the elements are between `lo` and
`hi`. Now if we implement `range`

> range :: Int -> Int -> [Int]
> range lo hi
>   | lo <= hi  = lo : range (lo + 1) hi
>   | otherwise = []

LiquidHaskell complains that `lo` is not *strictly* less than `hi`!

Fortunately, that's easily fixed, we'll just replace the `<=` in the guard with `<`.

> {-@ range' :: lo:Int -> hi:{Int | lo <= hi} -> {v:[Rng lo hi] | len v = hi - lo } @-}
> range' :: Int -> Int -> [Int]
> range' lo hi
>   | lo < hi   = lo : range' (lo + 1) hi
>   | otherwise = []


Holes
-----

Typing out the base Haskell types can be tedious, especially since GHC will
infer them. So we use `_` to represent a *type-hole*, which LiquidHaskell will
automatically fill in by asking GHC. For example, if we wrote a function
`rangeFind` with type

< (Int -> Bool) -> Int -> Int -> Maybe Int

we could write the refined type

> {-@ rangeFind :: _ -> lo:_ -> hi:{_ | lo <= hi} -> Maybe (Rng lo hi) @-}
> rangeFind f lo hi = find f $ range lo hi

Note that in order for `rangeFind` to type-check, LiquidHaskell has to infer
that `find` returns a `Maybe (Rng lo hi)` (show off liquid-pos-tip), which it
does by instantiating `find`s type parameter `a` with `Rng lo hi`.

Ok, we can talk about Integers, what about arbitrary, user-defined datatypes?

RJ:MOVE THIS INTO TOTALITY?

Measures
========
 
One of the most maligned Haskell functions is also one of the simplest.

> data List a = Nil | Cons a (List a)

> head (Cons x _) = x
> head Nil        = error "ARGH!!!!"

Many people argue that `head` and co. should be removed from the Prelude because
they're partial functions, and partial functions are dangerous.

With LiquidHaskell, we can specify *precisely* when it's safe to call `head`.

`head`'s pre-condition is that the input list be non-empty.

Lets see how to specify emptiness vs non-emptiness.

(Instead of defining an index that is baked into the type definition)
we'll define a *measure*, which you can think of as a *view* of the datatype.

> {-@ measure llen :: List a -> Int
>     llen (Nil)       = 0
>     llen (Cons x xs) = 1 + (llen xs)
>   @-}

Measures look like Haskell functions, but they're *not*. They are a very
restricted subset of inductively-defined Haskell functions with a single
equation per data constructor. LiquidHaskell translates measures into refined
types for the data constructors, e.g.

< Nil  :: {v:List a | llen v = 0}
< Cons :: _ -> xs:_ -> {v:List a | llen v = llen xs + 1}

ASIDE: another great spot to show off liquid-pos-tip.

> nil  = Nil
> cons = Cons

LiquidHaskell's interpretation of measures is a key distinction from indexed
data types, because we can define multiple measures independently of the actual
type definition, and LiquidHaskell will just conjoin the refinements arising
from the individual measures.

ASIDE: perhaps quickly show by defining `measure null` as a throwaway.

With our measure in hand we can now tell LiquidHaskell when it is safe to call
`head`.

> {-@ head :: {v:List a | llen v > 0} -> a @-}
> good_1 = head (Cons 1 Nil)
> bad_1  = head Nil

We can also give precise specifications to, e.g., `append`

> {-@ append :: xs:_ -> ys:_ -> {v:_ | llen v = llen xs + llen ys} @-}
> append Nil ys         = ys
> append (Cons x xs) ys = Cons x (append xs ys)

> safeZip :: (a -> b -> c) -> [a] -> [b] -> [c]
> safeZip f (x:xs) (y:ys) = f x y : safeZip f xs ys
> 


Refined Data Types
------------------

Sometimes we *want* every instance of a type to satisfy some invariant. Every
row in a `CSV` table should have the same number of columns.

> data CSV a = CSV { cols :: [String], rows :: [[a]] }
> {-@ type ListL a L = {v:[a] | len v = len L} @-}
> {-@ data CSV a = CSV { cols :: [String], rows :: [ListL a cols] } @-}

Since the invariant is *baked into* the refined type definition, LiquidHaskell
will reject *any* `CSV` value that does not satisfy the invariant.

> good_2 = CSV [ "Month", "Days"]
>              [ ["Jan", "31"]
>              , ["Feb", "28"] ]
> bad_2  = CSV  [ "Month", "Days"]
>               [ ["Jan", "31"]
>               , ["Feb"] ]


RJ:BEGIN-CUT

Refined Type-Classes
--------------------

Perhaps there's a common interface that we want multiple data types to support,
e.g. random-access. Many such interfaces have protocols that define how to
*safely* use the interface, like "don't index out-of-bounds". We can describe
these protocols in LiquidHaskell by packaging the functions into a type-class
and giving it a refined definition.

> class Indexable f where
>   size :: f a -> Int
>   at   :: f a -> Int -> a
>
> {-@
> class Indexable f where
>   size :: forall a. xs:f a -> {v:Nat | v = sz xs}
>   at   :: forall a. xs:f a -> {v:Nat | v < sz xs} -> a
> @-}

This poses a bit of a problem though, how do we define the `sz` measure?
Measures have to be defined for a specific datatype so LiquidHaskell can refine
the constructors. We'll work around this issue by introducing *type-indexed*
measures.

> {-@ class measure sz :: forall a. a -> Int @-}
> {-@ instance measure sz :: [a] -> Int
>     sz ([])   = 0
>     sz (x:xs) = 1 + (sz xs)
>   @-}
> {-@ invariant {v:[a] | sz v >= 0} @-}

Apart from allowing definitions for multiple types, class measures work just
like regular measures, i.e. they're translated into refined data constructor
types.

If we go ahead and define an instance for lists,

> instance Indexable [] where
>   size []        = 0
>   size (x:xs)    = 1 + size xs
>
>   (x:xs) `at` 0  = x
>   (x:xs) `at` i  = xs `at` (i-1)

LiquidHaskell will verify that our implementation matches the class
specification.

Clients of a type-class get to assume that the instances have been defined
correctly, i.e. LiquidHaskell will happily prove that 

> sum :: (Indexable f) => f Int -> Int
> sum xs = go 0 
>   where
>     go i | i < size xs = xs `at` i + go (i+1)
>          | otherwise   = 0

is safe for **all** instances of `Indexable`.


Abstract Refinements
--------------------

All of the examples so far have used *concrete* refinements, but sometimes
we just want to say that *some* property will be preserved by the function, e.g.

> max     :: Int -> Int -> Int 
> max x y = if x > y then x else y
>
> {-@ xPos  :: {v: _ | v > 0} @-}
> xPos  = max 10 13
>
> {-@ xNeg  :: {v: _ | v < 0} @-}
> xNeg  = max (0-5) (0-8)
>
> {-@ xEven :: {v: _ | v mod 2 == 0} @-}
> xEven = max 4 (0-6)

Since `max` returns one of it's arguments, we know that if *both* inputs share
some property, then *so will the output*. In LiquidHaskell we can express this
by abstracting over the refinements.

> {-@ max :: forall <p :: Int -> Prop>.
>            Int<p> -> Int<p> -> Int<p>
>   @-}

RJ:END-CUT

Now that we've covered the basics of using LiquidHaskell, let's take a look at
our first experiment: proving functions total.
