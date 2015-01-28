---
layout: post
title: "Okasaki's Lazy Queues"
date: 2015-01-28
comments: true
external-url:
author: Ranjit Jhala 
published: true
categories: measures
demo: LazyQueue.hs
---

The "Hello World!" example for fancy type systems is probably the
`append` function ("The output has size equal to the *sum* of the
inputs!").  One the one hand, its perfect: simple enough to explain
without pages of code, yet complex enough to show off dependency.
On the other hand, like the sweater I'm wearing right now, its a
bit well-worn and worse, was never wholly convincing
("Why do I *care* what the *size* of the output list is anyway?")

Recently, I came across a nice example that is almost as simple,
but is also well motivated: Okasaki's beautiful [Lazy Amortized Queues][okasaki95].
This structure relies leans heavily on an invariant to provide
fast *insertion* and *deletion*. Lets see how to enforce that
invariant with LiquidHaskell.

<!-- more -->

Queues
------

A [queue][queue-wiki] is a structure into which we can `insert` and `remove` data
such that the order in which the data is removed is the same as the order in which
it was inserted.

![A Queue](/images/queue.png)

To implement a queue *efficiently* one needs to have rapid access to both
the "head" as well as the "tail" because we `remove` elements from former
and `insert` elements into the latter. This is quite straightforward with
explicit pointers and mutation -- one uses an old school linked list and
maintains pointers to the head and the tail. But can we implement the
structure efficiently without having stoop so low?

Idea
----

Almost two decades ago, Chris Okasaki came up with a very cunning 
way to implement queues using a *pair* of *lazy lists* -- lets
call them `front` and `back` which represent the corresponding parts
of the Queue.


+ To `insert` elements, we just "cons" them onto the `back` list,
+ To `remove` elements, we just "un-cons" them from the `front` list.

`right` listcons` have to `` get "inserted" into the right list -- simply by a `cons`.

Intuitivelyone l
[queue-wiki]: http://en.wikipedia.org/wiki/Queue_%28abstract_data_type%29



\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--total"          @-}
{-@ LIQUID "--maxparams=3"    @-}

module LazyQueue where

-- Source: Okasaki, JFP 1995
-- http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf


--------------------------------------------------------------------------------
-- | Sized Lists
--------------------------------------------------------------------------------

data SList a = SL { size  :: Int
                  , elems :: [a]
                  }

{-@ type SListN a N = {v:SList a | size v = N} @-}

-- | Invariant: `size` is really the size:

{-@ data SList a = SL { size  :: Int
                      , elems :: {v:[a] | len v = size}
                      }
  @-}

-- | Size function actually returns the size: (Duh!)

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}

-- | Non-Empty Lists:

{-@ type NEList a = {v:SList a | size v > 0} @-}

{-@ nil          :: SListN a 0  @-}
nil              = SL 0 []

{-@ cons         :: a -> xs:SList a -> SListN a {size xs + 1}   @-}
cons x (SL n xs) = SL (n+1) (x:xs)

{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}
tl (SL n (_:xs)) = SL (n-1) xs
tl _             = die "never"

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x 
hd _             = die "never"


--------------------------------------------------------------------------------
-- | Sized Lists
--------------------------------------------------------------------------------

data Queue a = Q  { left   :: SList a
                  , right  :: SList a
                  }

-- | Invariant: `|right|` <= `|left|`

{-@ data Queue a = Q { left  :: SList a 
                     , right :: {v:SList a | size v <= size left}
                     }
  @-}

{-@ measure qsize @-}
qsize         :: Queue a -> Int
qsize (Q l r) = size l + size r

{-@ type QueueN a N = {v:Queue a | N = qsize v} @-}
{-@ type NEQueue a  = {v:Queue a | 0 < qsize v} @-}

{-@ emp :: QueueN a 0 @-}
emp = Q nil nil

insert e (Q l r) = makeq l (e `cons` r)

{-@ remove       :: q:NEQueue a -> (a, QueueN a {qsize q - 1}) @-}
remove (Q l r)   = (hd l, makeq (tl l) r)
  
{-@ makeq :: l:_ -> r:{_ | size r <= size l + 1} -> QueueN a {size l + size r} @-}
makeq l r
  | size r <= size l = Q l r
  | otherwise        = Q (rot l r nil) nil

{-@ rot :: l:_ -> r:SListN _ {1 + size l} -> a:_ -> {v:_ | size v = size l + size r + size a} @-}
rot l r a
  | size l == 0      = (hd r) `cons` a
  | otherwise        = (hd l) `cons` (rot (tl l) (tl r) ((hd r) `cons` a))

{-@ die :: {v:_ | false} -> a @-}
die x = error x

\end{code}




[okasaki95]: http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf
