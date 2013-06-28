---
layout: post
title: "Safely Catching A List By Its Tail"
date: 2013-01-31 16:12
author: Ranjit Jhala
published: true 
comments: true
external-url:
categories: measures 
demo: lenMapReduce.hs
---

[Previously][ref101] we [saw][ref102] some examples of how refinements
could be used to encode invariants about basic `Int` values.  Today, let's
see how refinements allow us specify and verify *structural invariants*
about recursive data types like lists. In particular, we will
learn about at a new mechanism called a `measure`, 
use measures to describe the **length** of a list, and 
use the resulting refinement types to obtain compile-time assurances
that canonical list manipulating operations like `head`, `tail`, `foldl1`
and (incomplete) pattern matches will not *blow up* at run-time.

<!-- more -->

\begin{code}
module ListLengths where

import Prelude hiding (length, map, filter, head, tail, foldl1)
import Language.Haskell.Liquid.Prelude (liquidError)
import qualified Data.HashMap.Strict as M
import Data.Hashable 
\end{code}

Measuring the Length of a List
------------------------------

To begin, we need some instrument by which to measure the length of a list.
To this end, let's introduce a new mechanism called **measures** which 
define auxiliary (or so-called **ghost**) properties of data values.
These properties are useful for specification and verification, but
**don't actually exist at run-time**.
That is, measures will appear in specifications but *never* inside code.




\begin{code} Let's reuse this mechanism, this time, providing a [definition](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/Base.spec) for the measure
measure len :: forall a. [a] -> GHC.Types.Int
len ([])     = 0
len (y:ys)   = 1 + (len ys) 
\end{code}

The description of `len` above should be quite easy to follow. Underneath the 
covers, LiquidHaskell transforms the above description into refined versions 
of the types for the constructors `(:)` and `[]`,
\begin{code}Something like 
data [a] where 
  []  :: forall a. {v: [a] | (len v) = 0 }
  (:) :: forall a. y:a -> ys:[a] -> {v: [a] | (len v) = 1 + (len ys) } 
\end{code}

To appreciate this, note that we can now check that

\begin{code}
{-@ xs :: {v:[String] | (len v) = 1 } @-}
xs = "dog" : []

{-@ ys :: {v:[String] | (len v) = 2 } @-}
ys = ["cat", "dog"]

{-@ zs :: {v:[String] | (len v) = 3 } @-}
zs = "hippo" : ys
\end{code}

Dually, when we *de-construct* the lists, LiquidHaskell is able to relate
the type of the outer list with its constituents. For example,

\begin{code}
{-@ zs' :: {v:[String] | (len v) = 2 } @-}
zs' = case zs of 
        h : t -> t
\end{code}

Here, from the use of the `:` in the pattern, LiquidHaskell can determine
that `(len zs) = 1 + (len t)`; by combining this fact with the nugget
that `(len zs) = 3` LiquidHaskell concludes that `t`, and hence, `zs'`
contains two elements.

Reasoning about Lengths
-----------------------

Let's flex our new vocabulary by uttering types that describe the
behavior of the usual list functions. 

First up: a version of the [standard][ghclist] 
`length` function, slightly simplified for exposition.

\begin{code}
{-@ length :: xs:[a] -> {v: Int | v = (len xs)} @-}
length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs
\end{code}

**Note:** Recall that `measure` values don't actually exist at run-time.
However, functions like `length` are useful in that they allow us to
effectively *pull* or *materialize* the ghost values from the refinement
world into the actual code world (since the value returned by `length` is
logically equal to the `len` of the input list.)

Similarly, we can speak and have confirmed, the types for the usual
list-manipulators like

\begin{code}
{-@ map      :: (a -> b) -> xs:[a] -> {v:[b] | (len v) = (len xs)} @-}
map _ []     = [] 
map f (x:xs) = (f x) : (map f xs)
\end{code}

and

\begin{code}
{-@ filter :: (a -> Bool) -> xs:[a] -> {v:[a] | (len v) <= (len xs)} @-}
filter _ []     = []
filter f (x:xs) 
  | f x         = x : filter f xs
  | otherwise   = filter f xs
\end{code}

and, since doubtless you are wondering,

\begin{code}
{-@ append :: xs:[a] -> ys:[a] -> {v:[a] | (len v) = (len xs) + (len ys)} @-}
append [] ys     = ys 
append (x:xs) ys = x : append xs ys
\end{code}

We will return to the above at some later date. Right now, let's look at
some interesting programs that LiquidHaskell can prove safe, by reasoning
about the size of various lists.



Example 1: Safely Catching A List by Its Tail (or Head) 
-------------------------------------------------------

Now, let's see how we can use these new incantations to banish, forever,
certain irritating kinds of errors. 
\begin{code}Recall how we always summon functions like `head` and `tail` with a degree of trepidation, unsure whether the arguments are empty, which will awaken certain beasts
Prelude> head []
*** Exception: Prelude.head: empty list
\end{code}

LiquidHaskell allows us to use these functions with 
confidence and surety! First off, let's define a predicate
alias that describes non-empty lists:

\begin{code}
{-@ predicate NonNull X = ((len X) > 0) @-}
\end{code}

Now, we can type the potentially dangerous `head` as:

\begin{code}
{-@ head   :: {v:[a] | (NonNull v)} -> a @-}
head (x:_) = x
head []    = liquidError "Fear not! 'twill ne'er come to pass"
\end{code}

As with the case of [divide-by-zero][ref101], LiquidHaskell deduces that
the second equation is *dead code* since the precondition (input) type
states that the length of the input is strictly positive, which *precludes*
the case where the parameter is `[]`.

Similarly, we can write

\begin{code}
{-@ tail :: {v:[a] | (NonNull v)} -> [a] @-}
tail (_:xs) = xs
tail []     = liquidError "Relaxeth! this too shall ne'er be"
\end{code}

Once again, LiquidHaskell will use the precondition to verify that the 
`liquidError` is never invoked. 

Let's use the above to write a function that eliminates stuttering, that
is which converts `"ssstringssss liiiiiike thisss"` to `"strings like this"`.

\begin{code}
{-@ eliminateStutter :: (Eq a) => [a] -> [a] @-}
eliminateStutter xs = map head $ groupEq xs 
\end{code}

The heavy lifting is done by `groupEq`

\begin{code}
groupEq []     = []
groupEq (x:xs) = (x:ys) : groupEq zs
                 where (ys,zs) = span (x ==) xs
\end{code}

which gathers consecutive equal elements in the list into a single list.
By using the fact that *each element* in the output returned by 
`groupEq` is in fact of the form `x:ys`, LiquidHaskell infers that
`groupEq` returns a *list of non-empty lists*. 
(Hover over the `groupEq` identifier in the code above to see this.)
Next, by automatically instantiating the type parameter for the `map` 
in `eliminateStutter` to `(len v) > 0` LiquidHaskell deduces `head` 
is only called on non-empty lists, thereby verifying the safety of 
`eliminateStutter`. (Hover your mouse over `map` above to see the
instantiated type for it!)

Example 2: Risers 
-----------------

The above examples of `head` and `tail` are simple, but non-empty lists pop
up in many places, and it is rather convenient to have the type system
track non-emptiness without having to make up special types. Let's look at a
more interesting example, popularized by [Neil Mitchell][risersMitchell]
which is a key step in an efficient sorting procedure, which we may return
to in the future when we discuss sorting algorithms.

\begin{code}
risers           :: (Ord a) => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc) = if x <= y then (x:s):ss else [x]:(s:ss)
    where 
      (s, ss)    = safeSplit $ risers (y:etc)
\end{code}

The bit that should cause some worry is `safeSplit` which 
simply returns the `head` and `tail` of its input, if they
exist, and otherwise, crashes and burns

\begin{code}
safeSplit (x:xs)  = (x, xs)
safeSplit _       = liquidError "don't worry, be happy"
\end{code}

How can we verify that `safeSplit` *will not crash* ?

The matter is complicated by the fact that since `risers` 
*does* sometimes return an empty list, we cannot blithely 
specify that its output type has a `NonNull` refinement.

Once again, logic rides to our rescue!

The crucial property upon which the safety of `risers` rests
is that when the input list is non-empty, the output list 
returned by risers is *also* non-empty. It is quite easy to clue 
LiquidHaskell in on this, namely through a type specification:

\begin{code}
{-@ risers :: (Ord a) 
           => zs:[a] 
           -> {v: [[a]] | ((NonNull zs) => (NonNull v)) } @-} 
\end{code}

Note how we relate the output's non-emptiness to the input's
non-emptiness,through the (dependent) refinement type. With this 
specification in place, LiquidHaskell is pleased to verify `risers` 
(i.e. the call to `safeSplit`).

Example 3: MapReduce 
--------------------

Here's a longer example that illustrates this: a toy *map-reduce* implementation.

First, let's write a function `keyMap` that expands a list of inputs into a 
list of key-value pairs:

\begin{code}
keyMap :: (a -> [(k, v)]) -> [a] -> [(k, v)]
keyMap f xs = concatMap f xs
\end{code}

Next, let's write a function `group` that gathers the key-value pairs into a
`Map` from *keys* to the lists of values with that same key.

\begin{code}
group kvs = foldr (\(k, v) m -> inserts k v m) M.empty kvs 
\end{code}

The function `inserts` simply adds the new value `v` to the list of 
previously known values `lookupDefault [] k m` for the key `k`.

\begin{code}
inserts k v m = M.insert k (v : vs) m 
  where vs    = M.lookupDefault [] k m
\end{code}

Finally, a function that *reduces* the list of values for a given
key in the table to a single value:

\begin{code}
reduce    :: (v -> v -> v) -> M.HashMap k [v] -> M.HashMap k v
reduce op = M.map (foldl1 op)
\end{code}

where `foldl1` is a [left-fold over *non-empty* lists][foldl1]

\begin{code}
{-@ foldl1      :: (a -> a -> a) -> {v:[a] | (NonNull v)} -> a @-}
foldl1 f (x:xs) =  foldl f x xs
foldl1 _ []     =  liquidError "will. never. happen."
\end{code}

We can put the whole thing together to write a (*very*) simple *Map-Reduce* library

\begin{code}
mapReduce   :: (Eq k, Hashable k) 
            => (a -> [(k, v)])    -- ^ key-mapper
            -> (v -> v -> v)      -- ^ reduction operator
            -> [a]                -- ^ inputs
            -> [(k, v)]           -- ^ output key-values

mapReduce f op  = M.toList 
                . reduce op 
                . group 
                . keyMap f
\end{code}

Now, if we want to compute the frequency of `Char` in a given list of words, we can write:

\begin{code}
{-@ charFrequency :: [String] -> [(Char, Int)] @-}
charFrequency     :: [String] -> [(Char, Int)]
charFrequency     = mapReduce wordChars (+)
  where wordChars = map (\c -> (c, 1)) 
\end{code}

You can take it out for a spin like so:

\begin{code}
f0 = charFrequency [ "the", "quick" , "brown"
                   , "fox", "jumped", "over"
                   , "the", "lazy"  , "cow"   ]
\end{code}

**Look Ma! No Types:** LiquidHaskell will gobble the whole thing up, and
verify that none of the undesirable `liquidError` calls are triggered. By
the way, notice that we didn't write down any types for `mapReduce` and
friends.  The main invariant, from which safety follows is that the `Map`
returned by the `group` function binds each key to a *non-empty* list of
values.  LiquidHaskell deduces this invariant by inferring suitable types
for `group`, `inserts`, `foldl1` and `reduce`, thereby relieving us of that
tedium. In short, by riding on the broad and high shoulders of SMT and
abstract interpretation, LiquidHaskell makes a little typing go a long way. 


Conclusions
-----------

Well folks, thats all for now. I trust this article gave you a sense of

1. How we can describe certain *structural properties* of data types, 
   such as the length of a list, 

2. How we might use refinements over these properties to describe key
   invariants and establish, at compile-time, the safety of operations that
   might blow up on unexpected values at run-time, and perhaps, most
   importantly,

3. How we can achieve the above, whilst just working with good old lists, 
   without having to [make up new types][risersApple] (which have the 
   unfortunate effect of cluttering programs with their attendant new 
   functions) in order to enforce special invariants.


[vecbounds]:  /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:    https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:     http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[risersMitchell]: http://neilmitchell.blogspot.com/2008/03/sorting-at-speed.html
[risersApple]: http://blog.jbapple.com/2008/01/extra-type-safety-using-polymorphic.html
[ref101]:  /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:  /blog/2013/01/27/refinements101-reax.lhs/ 

