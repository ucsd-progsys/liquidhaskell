---
layout: post
title: "Lexicographic Termination"
date: 2013-12-15 16:12
comments: true
external-url:
categories: termination, lexicographic ordering
author: Niki Vazou
published: true 
demo: LexicographicTermination.hs
---

[Previously][ref-termination] we saw how refinements can be used to prove termination
and we promised to extend our termination checker to handle "real-word" programs.

Keeping our promise, today we shall see a trick that allows liquidHaskell to prove termination on
more recursive functions, namely *lexicographic termination*.

<!-- more -->

<div class="hidden">

\begin{code}
module LexicographicTermination where

import Language.Haskell.Liquid.Prelude (liquidError)
\end{code}

</div>

Does Ackermann Function Terminate?
----------------------------------

Consider the famous [Ackermann
function](http://en.wikipedia.org/wiki/Ackermann_function)

\begin{code}
{-@ ack :: m:Nat -> n:Nat -> Nat @-}
ack :: Int -> Int -> Int
ack m n
    | m == 0          = n + 1
    | m > 0 && n == 0 = ack (m-1) 1
    | m > 0 && n >  0 = ack (m-1) (ack m (n-1))
    | otherwise       = liquidError "Bad arguments!!!"
\end{code}

Does `ack` terminate?

At each iteration

1. Either `m` decreases, 

2. or `m` remains the same and `n` decreases.

Each time that `n` reaches `0`, `m` decreases, so `m` will
eventaully reach `0` and `ack` will terminate.

Expressed more technically the pair `(m, n)`
decreases in the [lexicographic order](htpp://en.wikipedia/wiki/Lexicographic_order)
on pairs, which is a well-ordering, ie.,
we cannot go down infinitely many times.

Express Termination Metric
--------------------------

Great! The pair `(m, n)` is a *well-founded metric* on the Ackermann function that decreases.
From the [previous post][ref-termination] a well-founded metric is all
liquidHaskell needs to prove termination.
So, we should feed the tool with this information.

Remember the `Decrease` token?
We used it [previously][ref-termination]
to specify which is the decreasing argument.
Now, we will use it with more arguments to specify 
our decreasing pair. So,

\begin{code}
{-@ Decrease ack 1 2 @-}
\end{code}

says that the decreasing metric is the pair of the first
and the second arguments, 
ie., the pair `(m, n)`.

Finally, we will see how liquidHaskell uses this annotation to prove
termination.

Proving Termination By Types
----------------------------

Following once more our [previous post][ref-termination],
liquidHaskell typechecks the *body* of `ack` under an environment that
restricts `ack` to only be called on inputs *less than* `(m,n)`.
This time "less than" referes not to ordering on natural numbers, but to lexicographic
ordering
, i.e., using
an environment:

-  `m   :: Nat`
-  `n   :: Nat`
-  `ack :: m':Nat -> n':{v:Nat | m' < m || (m' = m && v < n)} -> Nat`

This ensures that any (recursive) call in the body only calls `ack` 
with inputs smaller than the current parameter `(m, n)`. Since its body 
typechecks in this environment, i.e. `ack` is called with smaller parameters, LiquidHaskell proves 
that `ack` terminates.


Someone may find the `Decrease` token annoying:
if we insert another argument we should also update the decrease information.
LiquidHaskell supports an alternative notation, 
which lets you annotate the type signature 
with a list of *decreasing expressions*.

\begin{code} So, `ack` will also typecheck against the signature:
{-@ ack :: m:Nat -> n:Nat -> Nat / [m, n] @-}
\end{code}

But what is the syntax of the decreasing expressions?
Are they restricted to function parameters?
No, but that is the subject of a next post!

[ref-lies]:        /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:      /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]: /blog/2013/12/08/termination-checking.lhs/
