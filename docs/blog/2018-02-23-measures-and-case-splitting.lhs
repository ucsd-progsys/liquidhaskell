---
layout: post
title: Measures and Case Splitting
date: 2018-02-23
comments: true
author: Niki Vazou
published: true
tags: measures, flags
demo: MeasuresAndCaseSplitting.hs
---

Liquid Haskell has a flag called `--no-case-expand`
which can make verification of your code much faster, 
especially when your code is using ADTs with many alternatives.
This flag says relax precision to get fast verification, 
thus may lead to rejecting safe code. 

In this post, I explain how `--no-case-expand` 
works using a trivial example!

(Click here to [demo][demo])

<!-- more -->


<div class="hidden">
\begin{code}

module MeasuresAndCaseSplitting where
\end{code}
</div>


Measures
---------

Let's define a simple data type with three alternatives 

\begin{code}
data ABC = A | B | C 
\end{code}

and a measure that turns `ABC` into an integer

\begin{code}
{-@ measure toInt @-}
toInt :: ABC -> Int 
toInt A = 1 
toInt B = 2
toInt C = 3 
\end{code}

Though obvious to us, Liquid Haskell will fail to check 
that `toInt` of any `ABC` argument
gives back a natural number. 
Or, the following call leads to a refinement type error. 

\begin{code}
{-@ unsafe :: x:ABC -> {o:() | 0 <= toInt x } @-}
unsafe     :: ABC -> () 
unsafe x   = ()
\end{code}

Why? 
By turning `toInt` into a measure, Liquid Haskell
gives precise information to each data constructor of `ABC`. 
Thus it knows that `toInt` or `A`, `B`, and `C`
is respectively `1`, `2`, and `3`, by *automatically* 
generating the following types: 

\begin{spec}
A :: {v:ABC | toInt v == 1 }
B :: {v:ABC | toInt v == 2 }
C :: {v:ABC | toInt v == 3 }
\end{spec}

Thus, to get the `toInt` information one need to 
explicitly perform case analysis on an `ABC` argument. 
The following code is safe

\begin{code}
{-@ safe :: x:ABC -> {o:() | 0 <= toInt x } @-}
safe     :: ABC -> ()
safe A   = () 
safe B   = () 
safe C   = () 
\end{code}

Liquid Haskell type check the above code because 
in the first case the body is checked under the assumption 
that the argument, call it `x`, is an `A`. 
Under this assumption, `toInt x` is indeed non negative. 
Yet, this is the case for the rest two alternatives, 
where `x` is either `B` or `C`. 
So, `0 <= toInt x` holds for all the alternatives, 
because case analysis on `x` automatically reasons about the 
value of the measure `toInt`. 


Now, what if I match the argument `x` only with `A`
and provide a default body for the rest?

\begin{code}
{-@ safeBut :: x:ABC -> {o:() | 0 <= toInt x } @-}
safeBut     :: ABC -> ()
safeBut A   = () 
safeBut _   = () 
\end{code}

Liquid Haskell knows that if the argument `x` is actually an `A`,
then `toInt x` is not negative, but does not know the value of `toInt`
for the default case. 

But, *by default* Liquid Haskell will do the the case expansion 
of the default case for you and rewrite your code to match `_`
with all the possible cases. 
Thus, Liquid Haskell will internally rewrite `safeBut` as 
\begin{code}
{-@ safeButLH :: x:ABC -> {o:() | 0 <= toInt x } @-}
safeButLH     :: ABC -> ()
safeButLH A   = () 
safeButLH B   = () 
safeButLH C   = () 
\end{code}

With this rewrite Liquid Haskell gets precision!
Thus, it has all the information it needs to prove `safeBut` as safe. 
Yet, it repeats the code of the default case, 
thus verification slows down. 

In this example, we only have three case alternatives, 
so we only repeat the code two times with a minor slow down. 
In cases with many more alternatives repeating the code 
of the default case can kill the verification time. 

For that reason, Liquid Haskell comes with the `no-case-expand`
flag that deactivates this expansion of the default cases. 
With the `no-case-expand` flag on, the `safeBut` code will not type check
and to fix it the user needs to perform the case expansion manually. 

In short, the `no-case-expand` increases verification speed 
but reduces precision. Then it is up to the user 
to manually expand the default cases, as required, 
to restore all the precision required for the code to type check. 

[demo]:              http://goto.ucsd.edu:8090/index.html#?demo=MeasuresAndCaseSplitting.hs


