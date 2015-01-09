---
title:         "Using LiquidHaskell"
author:        Ranjit Jhala
date:          Sep 5th, 2014
documentclass: book
toc:           true
bibliography: sw.bib
---


\begin{comment}
\begin{code}
module Introduction where
main = putStrLn "Ch3"
\end{code}
\end{comment}

Introduction {#intro}
============



One of the great things about Haskell is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping, in the bud, a large swathe of run-time errors.

Well-Typed Programs Do Go Wrong
-------------------------------

Alas, well-typed programs *do* go quite wrong, in a variety of ways.

\newthought{Division by Zero} This innocuous function computes the average
of a list of integers:

\begin{code}
average    :: [Int] -> Int
average xs = sum xs `div` length xs
\end{code}

When run with a non-empty list of numbers, we get the
desired result:

\begin{verbatim}
ghci> average [10, 20, 30, 40]
25
\end{verbatim}

However, if we call it with an empty list, we get a rather unpleasant crash:
\footnotetext{
We might solve this problem by writing \cc{average} more \emph{defensively},
perhaps returning a \cc{Maybe} or \cc{Either} value.
However, this merely kicks the can down the road.
Ultimately, we will 
want to extract the \cc{Int} from the \cc{Maybe} and if the inputs were
invalid to start with, then at that point we would be stuck with the same issue.
}
\begin{verbatim}
ghci> average []
*** Exception: divide by zero
\end{verbatim}

\newthought{Missing Keys}
Associative key-value maps are the new lists; they come "built-in"
with modern languages like Go, Python, JavaScript and Lua; and of
course, they're widely used in Haskell too.

\begin{verbatim}
ghci> :m +Data.Map 
ghci> let m = fromList [ ("haskell", "lazy")
                       , ("ocaml"  , "eager")]

ghci> m ! "haskell"
"lazy"
\end{verbatim}

Alas, maps are another source of vexing errors that are tickled
when we try to find the value of an absent key: 

\begin{verbatim} 
ghci> m ! "javascript"
"*** Exception: key is not in the map
\end{verbatim}

\footnotetext{Again, one could use a `Maybe` but its just deferring the inevitable.}

\newthought{Segmentation Faults}
Say what? How can one possibly get a segmentation fault with a *safe*
language like Haskell. Well, here's the thing: every safe language is
built on a foundation of machine code, or at the very least, `C`.
Consider the ubiquitous `vector` library:

\begin{shell}
ghci> :m +Data.Vector 
ghci> let v = fromList ["haskell", "ocaml"]
ghci> unsafeIndex v 0
"haskell"
\end{shell}

However, invalid inputs at the safe upper levels could percolate all
the way down and stir a mutiny down below:

\begin{verbatim}
ghci> unsafeIndex v 3
'ghci' terminated by signal SIGSEGV ...
\end{verbatim}

\footnotetext{Why use a function marked \cc{unsafe}?
First we have to thank the developers for carefully marking
it as such, because in general, given the many layers of abstraction,
it is hard to know which functions are indeed safe".
Second, because its very fast. Third, even if we used
the safe variant, we'd get a \emph{run-time} exception
which is only marginally better.}

\newthought{Heart Bleeds}
Finally, for certain kinds of programs, there is a fate worse than death.
`text` is a high-performance string processing library for Haskell, that
is used, for example, to build web services.

\begin{verbatim}
ghci> :m + Data.Text Data.Text.Unsafe 
ghci> let t = pack "Voltage"
ghci> takeWord16 5 t
"Volta"
\end{verbatim}

A cunning adversary can use invalid, or rather,
*well-crafted*, inputs that go well outside the size of
the given text` to read extra bytes and thus *extract secrets*
without anyone being any the wiser.

\begin{verbatim}
ghci> takeWord16 20 t
"Voltage\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{verbatim}

The above call returns the bytes residing in memory
*immediately after* the string `Voltage`. These bytes
could be junk, or could be either the name of your
favorite TV show, or, more worryingly, your bank
account password.

Refinement Types
----------------

Refinement types allow us to enrich Haskell's type system with
*predicates* which precisely describe the sets of *valid* inputs
and outputs of functions, and values held inside containers and
so on. These predicates are drawn from special *logics* for which
there are fast *decision procedures* called SMT solvers.

\newthought{By combining types with predicates} you can specify *contracts*
which describe valid inputs and outputs of functions. The refinement
type system *guarantees at compile time* that functions adhere to
their contracts. That is, you can rest assured that 
the above calamities *cannot occur at run-time*.

\newthought{LiquidHaskell} is a Refinement Type Checker for Haskell, and in
this document we'll describe how you can use it to make programs
and programming better.

\footnotetext{If you are familiar with the notion of Dependent Types,
for example, as in the Coq proof assistant, then Refinement Types
can be thought of as restricted class of the former where the logic
is restricted, at the cost of expressiveness, but with the reward of
a considerable amount of automation.}

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


Getting Started
---------------


First things first; lets see how to install and run LiquidHaskell.

\newthought{Dependencies}
LiquidHaskell requires, in addition to the cabal dependencies
the binary executable for an `SMTLIB2` compatible solver, e.g.
one of

+ [Z3](z3)
+ [CVC4](cvc4)
+ [MathSat](mathsat)
   
\newthought{Install}
Once you have the above on your system, simply do:

     $ cabal install liquidhaskell

\newthought{Run}
Once you have installed LiquidHaskell -- i.e. the binary `liquid` --
on your system, you can either use it at the command line, or
from within Emacs or Vim.

\newthought{Command Line} execution simply requires you type:

     $ liquid /path/to/file.hs

You will see a report of `SAFE` or `UNSAFE` together with type errors at
various points in the source.

\newthought{Emacs and Vim} have LiquidHaskell plugins, which run `liquid`
in the background as you edit any Haskell file, highlight errors, and
display the inferred types, all of which we find to be extremely useful.
Hence we *strongly recommend* these over the command line option.

+ Emacs' `flycheck` plugin is described  [here][liquid-emacs]
+ Vim's `syntastic` checker is described [here][liquid-vim]

Sample Code
-----------

This entire tutorial is written in literate Haskell.
All the code for it is available [on github][liquid-tutorial]
We *strongly* recommend you grab the code, and follow along
at home, and especially, that you do the various exercises.

[dml]:             http://www.cs.bu.edu/~hwxi/DML/DML.html
[vecspec]:         https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
[vec]:             http://hackage.haskell.org/package/vector
[agdavec]:         http://code.haskell.org/Agda/examples/Vec.agda
[ref101]:          /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:          /blog/2013/01/27/refinements-101-reax.lhs/ 
[data-list]:       http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html
[foldl]:           http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html
[listtail]:        /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[dmlarray]:        http://www.cs.bu.edu/~hwxi/academic/papers/pldi98.pdf
[liquid-tutorial]: http://github.com/ucsd-pl/liquidhaskell-tutorial.git 
[liquid-emacs]:    https://github.com/ucsd-progsys/liquidhaskell#emacs
[liquid-vim]:      https://github.com/ucsd-progsys/liquidhaskell#vim
[z3]:              http://z3.codeplex.com/
[cvc4]:            http://cvc4.cs.nyu.edu/ 
[mathsat]:         http://mathsat.fbk.eu/download.html
[smt-wiki]:        http://en.wikipedia.org/wiki/Satisfiability_Modulo_Theories
[hoogle-assert]:   https://www.haskell.org/hoogle/?hoogle=assert
[bst-wiki]:        http://en.wikipedia.org/wiki/Binary_search_tree
[vazou13]:         http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf
[smart-ctr-wiki]:  https://www.haskell.org/haskellwiki/Smart_constructors
[mitchell-riser]:  http://neilmitchell.blogspot.com/2008/03/sorting-at-speed.html
[apple-riser]:     http://blog.jbapple.com/2008/01/extra-type-safety-using-polymorphic.html
[safeList]:        /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[kmeansI]:         /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:        /blog/2013/02/17/kmeans-clustering-II.lhs/
[blog-set]:        /blog/2013/03/26/talking-about-sets.lhs/
[URL-take]:        https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:     http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:            http://www.youtube.com/watch?v=8uDuls5TyNE
[URL-kmeans]:      http://hackage.haskell.org/package/kmeans
[bird-pearls]: http://www.amazon.com/Pearls-Functional-Algorithm-Design-Richard/dp/0521513383
[hinze-icfp09]: http://www.cs.ox.ac.uk/ralf.hinze/publications/ICFP09.pdf
[smt-set]:       http://www.kroening.com/smt-lib-lsm.pdf)
[sbv]:      https://github.com/LeventErkok/sbv
[leon]:     http://lara.epfl.ch/w/leon

[setspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Set.spec
[mccarthy]: http://www-formal.stanford.edu/jmc/towards.ps
[z3cal]:    http://research.microsoft.com/en-us/um/people/leonardo/fmcad09.pdf
[xmonad-stackset]: http://hackage.haskell.org/package/xmonad-0.11/docs/XMonad-StackSet.html

[xmonad]:   http://xmonad.org/
[wiki-zipper]: http://en.wikipedia.org/wiki/Zipper_(data_structure)
