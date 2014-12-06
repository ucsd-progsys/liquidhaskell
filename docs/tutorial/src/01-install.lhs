

Getting Started
===============


First things first; lets see how to install and LiquidHaskell.

Dependencies 
------------

LiquidHaskell requires, in addition to the cabal dependencies

1. An `SMTLIB2` compatible solver executable, e.g. one of
    + [Z3](http://z3.codeplex.com/)
    + [CVC4](http://cvc4.cs.nyu.edu/) 
    + [MathSat](http://mathsat.fbk.eu/download.html)
   
2. A recent [`ocaml` compiler](http://caml.inria.fr/ocaml/release.en.html)

Install
-------

Once you have the above on your system, simply do:

    cabal install liquidhaskell

Run
---

Once you have installed LiquidHaskell -- i.e. the binary `liquid` --
on your system, you can either use it at the command line, or
from within Emacs or Vim.

\newthought{Command Line} execution simply requires you type:

    liquid /path/to/file.hs

You will see a report of `SAFE` or `UNSAFE` together with type errors at
various points in the source.

\newthought{Emacs} has an LiquidHaskell `flycheck` plugin, described here:

    https://github.com/ucsd-progsys/liquidhaskell#emacs

\newthought{Vim} has an LiquidHaskell `syntastic` checker, described here:

    https://github.com/ucsd-progsys/liquidhaskell#vim

The `Emacs` and `Vim` plugins run `liquid` in the background as you
edit any Haskell file, highlight errors, and display the inferred
types, all of which we find to be extremely useful, and hence
*strongly recommended* over the command line option.


\begin{comment}
\begin{code}
module Ch0 where

main = putStrLn "Hello"
\end{code}
\end{comment}

