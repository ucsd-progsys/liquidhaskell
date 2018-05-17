---
layout: post
title: The Hillelogram Verifier Rodeo I: LeftPad 
date: 2018-05-17
comments: true
author: Ranjit Jhala 
published: true
tags: reflection
demo: LeftPad.hs
---

A month ago, [Hillel Wayne](https://twitter.com/Hillelogram)
posted a three-part [verification challenge](https://twitter.com/Hillelogram/status/987432180837167104): 

<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">You have to provide a 100%, machine-checked guarantee that there are no problems with your code whatsoever. If it&#39;s so much easier to analyze FP programs than imperative programs, this should be simple, right?</p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432180837167104?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

While some of the problems might sound frivolous at first, 
in fact, they hit the sweet spot of being easy to describe,
and yet, tricky to implement and verify. I had a lot of fun 
hacking them up in LH, and learned a bunch of tricks in the 
process.

Today, lets see how to implement the first 
of these challenges -- `leftPad` -- in Haskell, 
and to check Hillel's specification with LH. 

(Click here to [demo][demo])

<!-- more -->

\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module PadLeft where 

import Prelude hiding (replicate, (++), (!!))
import Language.Haskell.Liquid.NewProofCombinators 
\end{code}



The LeftPad Challenge 
---------------------

The first of these problems was [leftPad](https://twitter.com/Hillelogram/status/987432181889994759)

<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">1. Leftpad. Takes a padding character, a string, and a total length, returns the string padded with that length with that character. If length is less than string, does nothing.<a href="https://t.co/X8qR8gTZdO">https://t.co/X8qR8gTZdO</a></p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432181889994759?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>


Implementation 
--------------

First, lets write an idiomatic implementation of `leftPad` where we 
will take the liberty of generalizing

- **padding character** to be the input `c` that is of some type `a` 
- **string** to be the input `xs` that is a list of `a`

If the target length `n` is indeed greater than the input string `xs`, 
i.e. if the `n - size xs` is positive, we `replicate` the character `c`
a suitable number of times, and append it to the left of the input.
If instead, `n` is smaller than `xs` we do nothing, i.e. return the input.

\begin{code}
{-@ reflect leftPad @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n c xs 
  | 0 < pad   = replicate pad c ++ xs 
  | otherwise = xs 
  where 
    pad       = n - size xs
\end{code}

The code for `leftPad` is short because we've delegated much of the work 
to the standard functions `size`, `replicate` and `++`. Here's how we 
can compute the `size` of a list:

\begin{code}
{-@ reflect size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0 
size (x:xs) = 1 + size xs
\end{code}

and here is the list append function `++` :

\begin{code}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {v:[a] | size v = size xs + size ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)
\end{code}

and finally the implementation of `replicate` :

\begin{code}
{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> {v:[a] | size v = n} @-}
replicate :: Int -> a -> [a]
replicate 0 _ = [] 
replicate n c = c : replicate (n - 1) c
\end{code}

What shall we "prove"? 
----------------------

My eyes roll -- more than a little --  whenever I read 
the phrase "proved X (a program) correct".

Why? Because there is no such thing as "correct".

There are only "specifications" or "properties", 
and proofs that ensures that your code matches 
those specifications.

What shall we prove about our implementation of `leftPad`?
One might argue that the above code is "obviously correct", 
i.e. the implementation more or less directly matches the 
informal requirements. Indeed, one way to formalize this 
"obviously correct" is to write a _specification_ that
capture's the informal requirements:

\begin{code}
{-@ leftPadObvious :: n:Int -> c:a -> xs:[a] -> 
      { leftPad n c xs = if (size xs < n) 
                            then replicate (n - size xs) c ++ xs 
                            else xs 
      } 
  @-}
leftPadObvious = () 
\end{code}

The [Idris solution][idris-leftpad] is especially terse 
because, it essentially says the specification _is_ the 
implementation.







The Importance of being Decidable 
---------------------------------

Our proof, _like_ the original Dafny solution, 
uses SMT solvers to automate verification.
However, unlike Dafny (and other SMT based verifiers), 
LH takes the somewhat fanatical stance about restricting 
all SMT queries to **decidable fragments**.


-----------------------------------------------------------------------------------
-- Properties 
-----------------------------------------------------------------------------------
{-@ thmPadLeft :: n:_ -> c:_ -> xs:{size xs < n} -> i:{Nat | i < n - size xs} 
               -> { (padLeft n c xs !! i) == (if (i < n - size xs) then c else (xs !! (i - (n - size xs)))) }                               
  @-}
thmPadLeft :: Int -> a -> [a] -> Int -> ()
thmPadLeft n c xs i 
  | i < n - size xs = thmAppLeft  (replicate (n - size xs) c) xs i &&& thmReplicate (n - size xs) c i   
  | otherwise       = thmAppRight (replicate (n - size xs) c) xs i

-----------------------------------------------------------------------------------
-- Theorems about Lists (these are baked in as 'axioms' in the dafny prelude) 
-- https://github.com/Microsoft/dafny/blob/master/Binaries/DafnyPrelude.bpl#L896-L1108
-----------------------------------------------------------------------------------

{-@ thmAppLeft :: xs:[a] -> ys:[a] -> {i:Nat | i < size xs} -> { (xs ++ ys) !! i == xs !! i } @-} 
thmAppLeft :: [a] -> [a] -> Int -> ()
thmAppLeft (x:xs)  ys 0 = () 
thmAppLeft (x:xs) ys i  = thmAppLeft xs ys (i-1)      

{-@ thmAppRight :: xs:[a] -> ys:[a] -> {i:Nat | size xs <= i} -> { (xs ++ ys) !! i == ys !! (i - size xs) } @-} 
thmAppRight :: [a] -> [a] -> Int -> ()
thmAppRight []     ys i = () 
thmAppRight (x:xs) ys i = thmAppRight xs ys (i-1)      

{-@ thmReplicate :: n:Nat -> c:a -> i:{Nat | i < n} -> { replicate n c !! i  == c } @-}
thmReplicate :: Int -> a -> Int -> () 
thmReplicate n c i 
  | n == 0    = () 
  | i == 0    = ()
  | otherwise = thmReplicate (n-1) c (i-1) 

-----------------------------------------------------------------------------------
-- Stuff from library Data.List 
-----------------------------------------------------------------------------------

{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> {v:[a] | size v = n} @-}
replicate :: Int -> a -> [a]
replicate 0 _ = [] 
replicate n c = c : replicate (n - 1) c

{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {v:[a] | size v = size xs + size ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0 
size (x:xs) = 1 + size xs

{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(!!) :: [a] -> Int -> a 
(x:_)  !! 0 = x 
(_:xs) !! n = xs !! (n - 1)

-----------------------------------------------------------------------------------
\end{code}

[idris-leftpad]: https://github.com/hwayne/lets-prove-leftpad/blob/master/idris/Leftpad.idr