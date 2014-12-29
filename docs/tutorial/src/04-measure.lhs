Measures
========


In the last two chapters, we saw how refinements could be used to
reason about the properties of basic `Int` values like vector
indices, or the elements of a list. Next, lets see how we can
describe properties of aggregate structures like lists and trees,
and use these properties to improve the APIs for operating over
such structures.

\begin{comment}
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}

module Measures where

import Prelude hiding(null, tail, head)

main = putStrLn "Hello"

-- | Old Definitions

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

-- Type Definitions
divide     :: Int -> Int -> Int
size1, size2 :: [a] -> Int
\end{code}
\end{comment}


Computing Averages
------------------

As a motivating example, let us return to problem of ensuring
the safety of division. Recall that we wrote:

\begin{code}
{-@ divide :: Int -> NonZero -> Int @-}
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n
\end{code}

\newthought{The Precondition} asserted by the input type `NonZero`
allows LiquidHaskell to prove that the `die` is *never* executed at
run-time, but consequently, requires us to establish that wherever
`divide` is *used*, the second parameter be provably non-zero.
This is requirement is not onerous when we know exactly what the
divisor is *statically*

\begin{code}
avg2 x y   = divide (x + y)     2

avg3 x y z = divide (x + y + z) 3
\end{code}

\noindent However, it can be more of a challenge when the divisor
is obtained *dynamically*. For example, lets write a function to
find the number of elements in a list

\begin{code}
size        :: [a] -> Int
size []     =  0
size (_:xs) =  1 + size xs
\end{code}

\noindent and use it to compute the average value of a list:

\begin{code}
avgMany xs = divide total elems 
  where
    total  = sum  xs
    elems  = size xs
\end{code}

Uh oh. LiquidHaskell wags its finger at us! 

\begin{liquiderror}
     src/04-measure.lhs:77:27-31: Error: Liquid Type Mismatch
       Inferred type
         VV : Int | VV == elems
      
       not a subtype of Required type
         VV : Int | 0 /= VV
      
       In Context
         VV    : Int | VV == elems
         elems : Int
\end{liquiderror}

Indeed, there is no way to prove that the divisor is `NonZero`,
because it *can* be `0` -- when the list is *empty*. Thus, we
need a way of specifying that the input to `avgMany` is indeed
non-empty!

Lifting Functions to Measures
-----------------------------

\newthought{How} shall we tell LiquidHaskell that a list is *non-empty*?

Recall the notion of `measure` previously [introduced](#vectorbounds)
to describe the size of a `Data.Vector`. In that spirit, lets write
a `measure` that computes whether a list is not empty:

\begin{code}
{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool 
notEmpty []    = False
notEmpty (_:_) = True 
\end{code}

A `measure` is simply a *total* Haskell function,

1. With a *single* equation per data constructor, and 
2. Guaranteed to terminate, via structural recursion.

The declaration `measure notEmpty` tells LiquidHaskell to *lift*
the function up into the refinement logic, allowing us to use it
inside refinements.


Using Measures
--------------

To use the newly defined measure, we define an alias for 
non-empty lists, i.e. the *subset* of plain old Haskell
lists `[a]` for which the predicate `notEmpty` holds
                
\begin{code}
{-@ type NEList a = {v:[a] | notEmpty v}      @-}
\end{code}


We can now refine the API to establish the safety of
the list-average function.

\newthought{Size} First, we specify that `size` returns
a non-zero value when the input list is not-empty:

\begin{code}
{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}
\end{code}

\newthought{Average} Second, we specify that the `average`
is only sensible for non-empty lists:

\begin{code}
{-@ average :: NEList Int -> Int @-}
average xs = divide total elems
  where
    total  = sum xs
    elems  = size xs
\end{code}

\exercise Fix the code below to obtain an alternate variant
`average'` that returns `Nothing` for empty lists:

\begin{code}
average' xs
  | ok        = Just $ divide total elems 
  | otherwise = Nothing 
  where
    total     = sum  xs
    elems     = size xs
    ok        = True    -- What expression goes here? 
\end{code}


\exercise An important aspect of formal verifiers like LiquidHaskell
is that they help establish properties not just of your *implementations*
but equally, or more importantly, of your *specifications*. In that spirit,
can you explain why the following two variants of `size` are *rejected*
by LiquidHaskell?

\begin{code}
{-@ size1    :: xs:(NEList a) -> Pos @-}
size1 []     =  0
size1 (_:xs) =  1 + size1 xs

{-@ size2    :: xs:[a] -> {v:Int | notEmpty xs => v > 0} @-}
size2 []     =  0
size2 (_:xs) =  1 + size2 xs
\end{code}

\todo{SOLUTION}



