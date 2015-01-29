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

The "Hello World!" example for fancy type systems is probably the sized vector
or list `append` function ("The output has size equal to the *sum* of the
inputs!").  One the one hand, its perfect: simple enough to explain without
pages of code, yet complex enough to show off whats cool about dependency. On
the other hand, like the sweater I'm sporting right now, its a bit well-worn and
worse, was never wholly convincing ("Why do I *care* what the *size* of the
output list is anyway?")

Recently, I came across a nice example that is almost as simple, but is also
well motivated: Okasaki's beautiful [Lazy Amortized Queues][okasaki95].  This
structure relies leans heavily on an invariant to provide fast *insertion* and
*deletion*. Lets see how to enforce that invariant with LiquidHaskell.

<!-- more -->

<div class="hidden">
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--total"          @-}
{-@ LIQUID "--maxparams=3"    @-}

module LazyQueue (Queue, insert, remove, emp) where

import Prelude hiding (length)

-- | Size function actually returns the size: (Duh!)

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}
data Queue a = Q  { front :: SList a
                  , back  :: SList a
                  }

-- Source: Okasaki, JFP 1995
-- http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf

\end{code}
</div>

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

Queues = Pair of Lists
----------------------

Almost two decades ago, Chris Okasaki came up with a very cunning way
to implement queues using a *pair* of lists -- lets call them `front`
and `back` which represent the corresponding parts of the Queue.

+ To `insert` elements, we just *cons* them onto the `back` list,
+ To `remove` elements, we just *un-cons* them from the `front` list.

The catch is that we need to shunt elements from the back to the
front every so often, e.g. when

1. a `remove` call is triggered, and
2. the `front` list is empty,

We can transfer the elements from the `back` to the `front`.

Okasaki observed that every element is only moved *once* from the
front to the back; hence, the time for `insert` and `lookup` could be
`O(1)` when *amortized* over all the operations. Awesome, right?!

Almost. Some set of unlucky `remove` calls (which occur when
the `front` is empty) are stuck paying the bill. They have a
rather high latency upto `O(n)` where `n` is the total number
of operations. Oops.

Queue = Balanced Lazy Lists
---------------------------

This is where Okasaki's beautiful insights kick in. Okasaki
observes that all we need to do is to enforce a simple invariant:

**Invariant:** Size of `front` >= Size of `back`

If now the lists are *lazy* i.e. only constructed as the head
value is demanded, then a single `remove` needs only a tiny `O(log n)`
in the worst case, and so no single `remove` is stuck paying the bill.

Lets see how to represent these Queues and ensure the crucial invariant(s)
with LiquidHaskell. What we need are the following ingredients:

1. A type for `List`s, and a way to track their `size`,

2. A type for `Queue`s which encodes the *balance* invariant -- ``front longer than back",

3. A way to implement the `insert`, `remove` and `transfer` operations.

Sized Lists
------------

The first part is super easy. Lets define a type:

\begin{code}
data SList a = SL { size :: Int, elems :: [a]}
\end{code}

We have a special field that saves the `size` because otherwise, we
have a linear time computation that wrecks Okasaki's careful
analysis. (Actually, he presents a variant which does *not* require
saving the size as well, but thats for another day.)

But how can we be sure that `size` is indeed the *real size* of `elems`?

Lets write a function to *measure* the real size:

\begin{code}
{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs
\end{code}

and now, we can simply specify a *refined* type for `SList` that ensures
that the *real* size is saved in the `size` field:

\begin{code}
{-@ data SList a = SL {
       size  :: Nat 
     , elems :: {v:[a] | realSize v = size}
     }
  @-}
\end{code}

As a sanity check, consider this:

\begin{code}
okList  = SL 1 ["cat"]    -- accepted

badList = SL 1 []         -- rejected
\end{code}

It is helpful to define a few aliases for `SList`s of a size `N` and
non-empty `SList`s:

\begin{code}
-- | SList of size N

{-@ type SListN a N = {v:SList a | size v = N} @-}

-- | Non-Empty SLists:

{-@ type NEList a = {v:SList a | size v > 0} @-}

\end{code}

Finally, we can define a basic API for `SList`.

**To Construct** lists, we use `nil` and `cons`:

\begin{code}
{-@ nil          :: SListN a 0  @-}
nil              = SL 0 []

{-@ cons         :: a -> xs:SList a -> SListN a {size xs + 1}   @-}
cons x (SL n xs) = SL (n+1) (x:xs)
\end{code}

**To Destruct** lists, we have `hd` and `tl`.

\begin{code}
{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}
tl (SL n (_:xs)) = SL (n-1) xs

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x 
\end{code}

Don't worry, they are perfectly *safe* as LiquidHaskell will make
sure we *only* call these operators on non-empty `SList`s. For example,

\begin{code}
okHd  = hd okList       -- accepted

badHd = hd (tl okList)  -- rejected
\end{code}


Queue Type
-----------

Now, it is quite straightforward to define the `Queue` type, as pair of lists,
`front` and `back` such that the latter is always smaller than the former:

\begin{code}
{-@ data Queue a = Q {
       front :: SList a 
     , back  :: SListLE a (size front)
     }
  @-}
\end{code}

Where the alias `SListLE a L` corresponds to lists with less than `N` elements:

\begin{code}
{-@ type SListLE a N = {v:SList a | size v <= N} @-}
\end{code}

As a quick check, notice that we *cannot represent illegal Queues*:

\begin{code}
okQ  = Q okList nil  -- accepted, |front| > |back| 

badQ = Q nil okList  -- rejected, |front| < |back|
\end{code}

**To Measure Queue Size** let us define a function

\begin{code}
{-@ measure qsize @-}
qsize         :: Queue a -> Int
qsize (Q l r) = size l + size r
\end{code}

This will prove helpful to define `Queue`s of a given size `N` and
non-empty `Queue`s (from which values can be safely removed.)

\begin{code}
{-@ type QueueN a N = {v:Queue a | N = qsize v} @-}
{-@ type NEQueue a  = {v:Queue a | 0 < qsize v} @-}
\end{code}


Queue Operations
----------------

Almost there! Now all that remains is to define the `Queue` API. The
code below is more or less identical to Okasaki's (I prefer `front`
and `back` to his `left` and `right`.)


**The Empty Queue** is simply one where both `front` and `back` are `nil`.

\begin{code}
{-@ emp :: QueueN a 0 @-}
emp = Q nil nil
\end{code}

**To Insert** an element we just `cons` it to the `back` list, and call
the *smart constructor* `makeq` to ensure that the balance invariant holds:

\begin{code}
{-@ insert       :: a -> q:Queue a -> QueueN a {qsize q + 1}   @-}
insert e (Q f b) = makeq f (e `cons` b)
\end{code}

**To Remove** an element we pop it off the `front` by using `hd` and `tl`.
Notice that the `remove` is only called on non-empty `Queue`s, which together
with the key balance invariant, ensures that the calls to `hd` and `tl` are safe.

\begin{code}
{-@ remove       :: q:NEQueue a -> (a, QueueN a {qsize q - 1}) @-}
remove (Q f b)   = (hd f, makeq (tl f) b)
\end{code}

*Aside:* Why didn't we (or Okasaki) use a pattern match here?

**To Ensure the Invariant** we use the smart constructor `makeq`,
which is where the heavy lifting, such as it is, happens. The
constructor takes two lists, the front `f` and back `b` and if they
are balanced, directly returns the `Queue`, and otherwise transfers
the elements from `b` over using `rot`ate.

\begin{code}
{-@ makeq :: f:SList a
          -> b:SListLE a {size f + 1 }
          -> QueueN a {size f + size b}
  @-}
makeq l r
  | size r <= size l = Q l r
  | otherwise        = Q (rot l r nil) nil
\end{code}

**The Rotate** function is only called when the `back` is one larger
than the `front` (we never let things drift beyond that). It is
arranged so that it the `hd` is built up fast, before the entire
computation finishes; which, combined with laziness provides the
efficient worst-case guarantee.

\begin{code}
{-@ rot :: l:SList a
        -> r:SListN _ {1 + size l}
        -> a:SList _
        -> SListN _ {size l + size r + size a}
  @-}
rot l r a
  | size l == 0 = (hd r) `cons` a
  | otherwise   = (hd l) `cons` (rot (tl l) (tl r) ((hd r) `cons` a))
\end{code}

Conclusion
----------

Well there you have it; Okasaki's beautiful lazy Queue, with the
invariants easily expressed and checked with LiquidHaskell. I find
this example particularly interesting because the refinements express
invariants that are critical for efficiency, and furthermore the code
introspects on the `size` in order to guarantee the invariants.  Plus,
its just marginally more complicated than `append` and so, (I hope!)
was easy to follow.



[okasaki95]: http://www.westpoint.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/jfp95queue.pdf

[queue-wiki]: http://en.wikipedia.org/wiki/Queue_%28abstract_data_type%29
