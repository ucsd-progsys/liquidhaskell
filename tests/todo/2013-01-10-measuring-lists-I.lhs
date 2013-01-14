---
layout: post
title: "Measuring Lists I"
date: 2013-01-05 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic
demo: lenMapReduce.hs
---

[Previously][vecbounds] we saw how liquid refinements can be pretty 
handy for enforcing invariants about integers, for example the about 
whether a `Vector` is being indexed within bounds. Now, lets see how
they can be used to encode structural invariants about data types, in
particular, lets see how to use the `measure` mechanism to talk about 
the **size** of a list, and thereby write safe versions of potentially
list manipulating functions.

<!-- more -->

\begin{code}
module ListLengths where

import Prelude hiding (length, map, filter, head, tail, foldl1)
-- import Language.Haskell.Liquid.Prelude (liquidError)
import qualified Data.HashMap.Strict as M
import Data.Hashable 

liquidError = error 
\end{code}

Measuring the Length of a List
------------------------------

To begin, we need some instrument by which to measure the length of a list.
[Recall][vecbounds] the auxiliary functions used to represent the number of 
elements of a `Vector`. Lets reuse this mechanism, this time, providing a 
[definition](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/Base.spec)
for the measure

\begin{code}Specifying the length of a list 
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

Hover your mouse over the `:` and `[]` above to confirm their types!

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

Great! Lets flex our new vocabulary by uttering types that describe the
behavior of the usual list functions. 

First up: a somewhat simplified version of the [standard library's][ghclist] 
`length` from, slightly simplified for exposition.

\begin{code}
{-@ length :: xs:[a] -> {v: Int | v = (len xs)} @-}
length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs
\end{code}

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

and, since, doubtless you are wondering,

\begin{code}
{-@ append :: xs:[a] -> ys:[a] -> {v:[a] | (len v) = (len xs) + (len ys)} @-}
append [] ys     = ys 
append (x:xs) ys = x : append xs ys
\end{code}

Warm Up: Safely Catching A List by The `head` (or `tail`)
---------------------------------------------------------

Now, lets see how we can use these new incantations to banish, forever,
certain irritating kinds of errors. To wit, recall how we always summon 
functions like `head` and `tail` with a degree of trepidation, unsure
whether the arguments are empty, which will awaken certain beasts

```
Prelude> head []
*** Exception: Prelude.head: empty list
```

Well, now LiquidHaskell can allow us to use these functions with confidence
and surety, once we type them as:

\begin{code}
{-@ head   :: {v:[a] | (len v) > 0} -> a @-}
head (x:_) = x
head []    = liquidError "Fear not! 'twill ne'er come to pass"
\end{code}

As with the case of [divide-by-zero][ref101], LiquidHaskell deduces that
the second equation is *dead code* since the precondition (input) type
states that the length of the input is strictly positive, which *precludes*
the case where the parameter is `[]`.

Similarly, we may write

\begin{code}
{-@ tail :: {v:[a] | (len v) > 0} -> [a] @-}
tail (_:xs) = xs
tail []     = liquidError "Relaxeth! this too shall ne'er be"
\end{code}

Once again, LiquidHaskell will use the precondition to verify that the 
`liquidError` is never invoked. 

Lets use the above to write a function that eliminates stuttering, that
is which converts "ssstringssss liiiiiike thisss"` to "strings like this".

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

(Put your mouse over the `groupEq` identifier in the code above to see this.)

Next, by automatically instantiating the type parameter for the `map` 
in `eliminateStutter` to `(len v) > 0` LiquidHaskell deduces `head` 
is only called on non-empty lists, thereby verifying the safety of 
`eliminateStutter`.


A Longer Example: MapReduce 
---------------------------

The above examples of `head` and `tail` are simple, but non-empty lists pop
up in many places, and it is rather convenient to have the type system
track non-emptiness without having to make up special types. Here's a
longer example.

First, lets write a function `keyMap` that expands a list of inputs into a 
list of key-value pairs:

\begin{code}
keyMap :: (a -> [(k, v)]) -> [a] -> [(k, v)]
keyMap f xs = concatMap f xs
\end{code}

Next, lets write a function `group` that gathers the key-value pairs into a
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

Finally, we can write a function that *reduces* the list of values for a given
key in the table to a single value:

\begin{code}
reduce    :: (v -> v -> v) -> M.HashMap k [v] -> M.HashMap k v
reduce op = M.map (foldl1 op)
\end{code}

where `foldl1` is a [left-fold over *non-empty* lists][foldl1]

\begin{code}
foldl1 f (x:xs) =  foldl f x xs
foldl1 _ []     =  liquidError "will. never. happen."
\end{code}

We can put the whole thing together to write a (*very*) simple *Map-Reduce* library

\begin{code}
{-@ mapReduce   :: (Eq k, Hashable k) 
                => (a -> [(k, v)]) -- ^ key-mapper
                -> (v -> v -> v)   -- ^ reduction operator
                -> [a]             -- ^ inputs
                -> [(k, v)]        -- ^ output key-values
  @-}

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


LiquidHaskell will gobble the whole thing up, and verify that none of the
undesirable `liquidError` calls are triggered. 

Conveniently, we *needn't write down any types* for `mapReduce` and friends. 

The main invariant, from which safety follows is that the `Map` 
returned by the `group` function binds each key to a *non-empty* list 
of values. LiquidHaskell deduces this invariant by inferring suitable 
types for `group`, `inserts`, `foldl1` and `reduce`, thereby relieving 
us of that tedium. 

In short, by riding on the broad and high shoulders of SMT, LiquidHaskell 
makes a little typing go a long way.



[vecbounds]:  /blog/2012/01/05/bounding-vectors.lhs/ 
[ghclist]  : https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[ref101]   :  /blog/2013/01/01/refinement-types-101.lhs/ 

[foldl1]   : http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
