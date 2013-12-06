---
layout: post
title: "Termination Checking II : Lexicographic Termination"
date: 2013-12-15 16:12
comments: true
external-url:
categories: termination, lexicographic ordering
author: Niki Vazou
published: true
demo: Termination2.hs
---

[Previously][ref-termination] we saw how refinements can be used to prove termination
and we promised to extend our termination checker to handle "real-word" programs.

Keeping our promise, today we shall see a trick that allows liquidHaskell to prove termination on
more recursive functions, namely *lexicographic termination*.

<!-- more -->

\begin{code}
module LexicographicTermination where

import Language.Haskell.Liquid.Prelude (liquidError)
\end{code}

Does Ackermann Function Terminate?
----------------------------------

Consider the famous [Ackermann
function](en.wikipedia.org/wiki/Ackermann_function)

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

It does, as at each iteration

1. Either `m` decreases, 

2. or `m` remains the same and `n` decreases.

Each time that `n` reaches `0`, `m` decreases, so both `n` and `m` will
eventaully reach `0`.

Expressed more technically the pair `(m, n)`
decreases in the [lexicographic order](en.wikipedia/wiki/Lexicographic_order)
on pairs, which is a well-ordering.
This means that we cannot go down in the infinitely many times.

Express Termination Metric
--------------------------

Great! We do have a *well-founded metric* on the Ackermann function that decreases.
Now we should feed liquidHaskell with this information.

Remember the `Decrease` token?
We used it in the [previous post][ref-termination]
to specify which is the decreasing argument.
Now, we can use with many more arguments to specify 
our decreasing pair. So,

\begin{code}
{-@ Decrease ack 1 2 @-}
\end{code}

says that the decreasing metric is the pair of the first
and the second argument, 
ie., the pair `(m, n)` 

Finally, we will see how liquidHaskell translates this annotation.

Proving Termination By Types
----------------------------

Again, following our [previous post][ref-termination],
liquidHaskell typechecks the *body* of `ack` under an environment that
restricts `ack` to only be called on inputs less than `(m,n)`.
But, instead of ordering on natural numbers, it uses lexicographic
ordering
, i.e., using
an environment:

-  `m   :: Nat`
-  `n   :: Nat`
-  `ack :: m':Nat -> n':{v:Nat | m'<m || (m'=m && v < n)} -> Nat`

This ensures that any (recursive) call in the body only calls `ack` 
with inputs smaller than the current parameter `(m, n)`. Since its body 
typechecks in this environment, i.e. `ack` is called with smaller parameters, LiquidHaskell proves 
that `ack` terminates.


Someone may find the `Decrease` token annoying:
if we insert another argument we should also update the decrease information.
LiquidHaskell supports an alternative notation, 
which let you annotate the type signature 
with a list of *decreasing expressions*.

\begin{code} So, `ack` will type against the signature:
{-@ ack :: m:Nat -> n:Nat -> Nat / [m, n]@-}
\end{code}

But what is the syntax of the decreasing expressions?
Are they restricted to function parameters?
No, but that is the subject of our next post!

[ref-lies]:        /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]:      /blog/2013/12/01/getting-to-the-bottom.lhs/
[ref-termination]: /blog/2013/12/08/termination-checking-1.lhs/
