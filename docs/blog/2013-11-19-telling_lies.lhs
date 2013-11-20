---
layout: post
title: "LiquidHaskell Caught Telling Lies!"
date: 2013-11-19 16:12
comments: true
external-url:
categories: termination
author: Niki Vazou
published: true
demo: TellingLies.hs
---

If you used liquidHaskell lately, you may have noticed some type errors that
just make no sense.
Well, that is not a bug, but a ... **termination checker** failing to prove that
your function terminates.

LiquidHaskell, *by default*, performs a termination check while verifying your
code.
Of course the tool would be useless if it required all your functions
to terminate.
Instead, it just requires that non-terminating functions return unrefined
results.
We will shortly explain when and how one can turn off termination checking while preserve
sound type checking.
To do so, we should start by explaining why termination is requied. 
<!-- more -->

\begin{code}
module TellingLies where

import Prelude  hiding (repeat)
import Language.Haskell.Liquid.Prelude (liquidAssert)
\end{code}

Why is Termination Analysis Required
-------------------------------------

Consider a no-terminating function:

\begin{code}
{-@ foo :: Int -> {v:Int | false} @-}
foo     :: Int -> Int
foo n   = foo n
\end{code}

According to the *partial correctness property*
the type signature for `foo` means that any
value `foo` returns will satisfy the result refinement
`false`. 
Since `foo` never returns, 
it can return *none* value, thus it trivially satisfies its
type.

Now, in an environment where `false` (i.e., `foo`'s result)
exists, liquidHaskell can prove anything, 
even the contradiction `0==1`:

\begin{code}
prop = liquidAssert ((\_ -> 0==1) (foo 0))
\end{code}

This is totally valid under *eager* evaluation, where
to execute the assertion one should first compute the argument
`foo 0` which never returns.
But, it is not valid under haskell's *lazy* semantics
where execution ignores the unused argument, and fails.

From the above discussion we see that partial correctness is not enough to
verify Haskell's lazy code.
To restore soundness we require *total correctness*, or
that each function terminates.
This explains why termination checking is set as default to liquidHaskell (as is
in many other verifiers, like Coq or Agda.)

Turning off Termination Checking
--------------------------------

Of course, you cannot prove termination of functions like `repeat`

\begin{code}
{-@ repeat :: a -> [a] @-}
repeat     :: a -> [a]
repeat a   = a : repeat a
\end{code}

Instead, you can mark `repeat` as `Lazy` to disable termination for these
functions:
\begin{code}
{-@ Lazy repeat @-}
\end{code}

But, be careful!
By marking a function as `Lazy` *you* also guarantee that *the result type
cannot contain inconsistencies*.
In our previous example, liquidHaskell typechecked the unsafe `prop`, just
because we marked `foo` (who's return type contains inconsistency) as `Lazy`
\begin{code}
{-@ Lazy foo @-}
\end{code}

Even though it is hard to decide if a type can contain inconsistencies,
trivially *unrefined types* (or types refined to `true`) cannot ever be resolved
to `false`.
In other words, it is always safe to mark as `Lazy` functions with unrefined
result.

\begin{code}Finally, you have the option to totally disable termination checking, using the `no-termination` flag:
{-@ LIQUID "--no-termination" @-}
\end{code}


Prevent liquidHaskell from Telling Lies
---------------------------------------

In this post, we saw why termination is required for sound type checking and when
it is safe to deactivate it.
But still, we didn't discuss how to prevent the tool from telling lies, i.e., how
to actually prove termination.
Turns out that liquidHaskell is powerful enough to prove
termination on a great number of functions, but this is a topic of another post.
