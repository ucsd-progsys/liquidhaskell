---
title:         "LiquidHaskell"
author:        Ranjit Jhala
date:          Sep 5th, 2014
documentclass: book
toc:           true
---

\begin{code}
module Ch3 where
main = putStrLn "Ch3"
\end{code}


Introduction
============

One of the great things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping, in the bud, a large swathe of run-time errors.

Well-typed Programs Go Wrong
----------------------------

Alas, well-typed programs \emph{do} go quite wrong, in a variety of ways.

**Division by Zero**

Consider this innocuous function that averages a list of integers.

\begin{code}
average    :: [Int] -> Int
average xs = sum xs `div` length xs
\end{code}

If we run it with a \emph{valid}, non-empty list of numbers, we get the
desired result:

\begin{verbatim}
ghci> average [10, 20, 30, 40]
25
\end{verbatim}

But if we call it with an \emph{invalid} input,

\begin{verbatim}
ghci> average []
*** Exception: divide by zero
\end{verbatim}

we get a rather unpleasant and unexpected crash.
We might solve this problem by writing `average` more 
*defensively*, perhaps returning a `Maybe` or `Either` value.
However, this merely kicks the can down the road, as ultimately,
we're going to want to extract the integer from the `Maybe` and
if the inputs were invalid to start with, then at that point
we'd be stuck.

**Missing Keys**

Key-value maps are the new lists. They are important enough to have
become the backbone of modern languages like Go, Python, JavaScript
and Lua, and of course, they're widely used in Haskell too.

\begin{verbatim}
ghci> :m +Data.Map 
ghci> let m = fromList [ ("haskell", "lazy")
                       , ("ocaml"  , "eager")]

ghci> m ! "haskell"
"lazy"
\end{verbatim}

Alas, these maps are another source of vexing errors that are tickled
when we try to find the value of a key that is absent from the map.

\begin{verbatim} 
ghci> m ! "javascript"
"*** Exception: key is not in the map
\end{verbatim}

Again, one could use a `Maybe` but its just deferring the inevitable.

**Segmentation Faults**

Say what? How can one possibly get a segmentation fault with a *safe*
language like Haskell. Well, here's the thing: every safe language is
built on a foundation of machine code, or at the very least, `C`.
For example, consider the ubiquitous `vector` library:

\begin{verbatim}
ghci> :m +Data.Vector 
ghci> let v = fromList ["haskell", "ocaml"]
ghci> unsafeIndex v 0
"haskell"
\end{verbatim}

However, invalid inputs at the safe upper levels could percolate all
the way down and stir a mutiny down below:

\begin{verbatim}
ghci> unsafeIndex v 3

'ghci' terminated by signal SIGSEGV ...
\end{verbatim}

Of course, you might wonder, why would one use a function marked `unsafe`?
Well, first we have to thank the developers for carefully marking it as such,
because in general, given the many layers of abstraction, it is hard to know
which functions are indeed "safe". Second, because its very fast.
Third, even if we used the safe variant, we'd get a *run-time*
exception which is only marginally better.

**Heart Bleeds**

Finally, for certain kinds of programs, there is a fate worse than death.
`text` is a high-performance string processing library for Haskell, that
is used, for example, to build web services.

\begin{verbatim}
ghci> :m + Data.Text Data.Text.Unsafe 
ghci> let t = pack "Voltage"
ghci> takeWord16 5 t
"Volta"
\end{verbatim}

However, a cunning adversary can use an invalid, or shall we say
well-crafted, inputs that go well outside the size of the given
text, to read extra bytes and thus *extract secrets* without anyone
being any the wiser.

\begin{verbatim}
ghci> takeWord16 20 t
"Voltage\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{verbatim}

That is, the above call returns the bytes residing in memory immediately
after the string `Voltage`, which could be either the name of your favorite
TV show, or, more worryingly, your bank account password.


Refinement Types
----------------

Refinement types allow us to enrich Haskell's type system with
*predicates* which precisely describe the sets of *valid* inputs
and outputs of functions, and values held inside containers and
so on. These predicates are drawn from special *logics* for which
there are fast *decision procedures* called SMT solvers.

By combining types with predicates, you can specify *contracts*
which describe valid inputs and outputs of functions. The refinement
type system *guarantees at compile time* that functions adhere to
their contracts. That is, you can rest assured that 
the above calamities *cannot occur at run-time*.

LiquidHaskell is a Refinement Type Checker for Haskell, and in
this document we'll describe how you can use it to make programs
and programming better.

**Note:** If you are familiar with the notion of *Dependent Types*,
for example, as in the Coq proof assistant, then Refinement Types
can be thought of as restricted class of the former where the logic
is restricted, at the cost of expressiveness, but with the reward of
a considerable amount of automation.


Audience
--------

Do you

* know a bit of basic arithmetic and logic?
* know the difference between a `nand` and an `xor`?
* know any typed languages e.g. ML, Haskell, Scala, F# or Racket?
* know what `forall a. a -> a` means?
* like it when your code editor politely points out infinite loops?
* like your programs to not have bugs?

Then this tutorial is for you!

Sample Code
-----------

All the code for this tutorial is available at

    http://github.com/ucsd-pl/liquidhaskell-tutorial.git 

We *strongly* recommend you grab the code, and follow along
at home, and especially, that you do the various suggested
exercises.
