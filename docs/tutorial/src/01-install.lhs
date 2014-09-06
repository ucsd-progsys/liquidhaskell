Getting Started
===============

Dependencies 
------------

+ Z3
+ Ocaml


Install
-------

+ cabal install liquidhaskell

Run
---

+ cabal install
+ emacs

\begin{comment}

\begin{code}
module Ch0 where

main = putStrLn "Hello"
\end{code}

\begin{code}
{-@ fac :: Nat -> Nat @-}
fac :: Int -> Int
fac 0 = 1
fac n = n * fac (n - 1)
\end{code}

\end{comment}
