---
layout: post
title: "Refinements 101 (contd.)" 
date: 2013-01-27 16:12
author: Ranjit Jhala
published: true 
comments: true
external-url:
categories: basic
demo: refinements101reax.hs
---

Hopefully, the [previous][ref101] article gave you a basic idea about what
refinement types look like. Several folks had interesting questions, that
are worth discussing in a separate post.

<!-- more -->

\begin{code}
module Refinements101Reax where
\end{code}

How to relate outputs and inputs 
--------------------------------

Recall the function `divide`

\begin{code}
{-@ divide :: Int -> {v: Int | v /= 0 } -> Int @-}
divide     :: Int -> Int -> Int
divide n 0 = error "divide by zero"
divide n d = n `div` d
\end{code}

and `abz` was the absolute value function

\begin{code}
abz               :: Int -> Int
abz n | 0 < n     = n
      | otherwise = 0 - n
\end{code}

[nanothief](http://www.reddit.com/user/nanothief) [remarked][qreddit101]
that LiquidHaskell was unable to verify the safety of the following 
divide-by-zero 

\begin{code}
{-@ f :: Int -> Int @-}
f x | abz x == 0 = 3
    | otherwise = 3 `divide` x
\end{code}

Nanothief correctly argues that the code is clearly safe as 

    "`abz x == 0` being false implies `x /= 0`"

Indeed, the code *is safe*, however, the reason that LiquidHaskell rejected
it has nothing to do with the inability to  

    "track the constraints of values based on tests using new values derived from that value".

as Nanothief surmises, but instead, because LiquidHaskell supports
**modular verification** where the *only* thing known about `abz` is 
whatever is specified in its *type*. The type

~~~~~{.haskell}
abz :: Int -> {v: Int | 0 <= v }
~~~~~
 
is rather anemic, in that it tells us nothing about the *relationship*
between the output and input. In particular, the type does not say that
when the *output* is non-zero, the *input* must also have been non-zero.

Instead, we can write a *stronger* type which *does* capture this
information, for example

~~~~~{.haskell}
abz :: x:Int -> {v:Int | v = (if (x > 0) then x else (0 - x))}
~~~~~

where 

~~~~~{.haskell}
v = if p then e1 else e2
~~~~~

is an abbreviation forthe logical formula 

~~~~~{.haskell}
(p => v == e1) && ((not p) => v = e2)
~~~~~

With this specification for `abz`, LiquidHaskell is able to reason that
when `abz x` is non-zero, `x` is also non-zero. Of course, `abz` is trivial 
enough that we can very precisely capture its *exact* semantics in the 
refinement type, but thats is rarely the case. 

Nevertheless, even here, you could write a somewhat *weaker* specification,
that still had enough juice to allow the verification of the `divide` call
in `f`. In particular, we might write

\begin{code}
{-@ abz :: x:Int -> {v:Int | ((0 <= v) && ((v = 0) <=> (x = 0))) } @-}
\end{code}

which states the output is `0` *if and only if* the input is `0`.
LiquidHaskell will happily verify that `abz` implements this specification,
and will use it to verify the safety of `f` above.

How to tell a Fib
-----------------

[Chis Done](https://twitter.com/christopherdone) [asked][qblog101]
why LiquidHaskell refused to verify the following definition of `fib`.

\begin{code}
{-@ fib :: n:Int -> { b:Int | (n >= 0 && b >= n) } @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
\end{code}

Indeed, the both the *specification* and the *implementation* look pretty
legit, so what gives? (btw, follow the link above to *demo this code* 
yourself.) It turns out that there are *two* different reasons why. 

**Reason 1: Assumptions vs. Guarantees**

What we really want to say over here is that the *input* `n` 
is non-negative. However, putting the refinement `n >= 0` in 
the *output* constraint means that it becomes something that 
LiquidHaskell checks that the function `fib` **guarantees** 
(or **ensures**).
That is, the type states that we can pass `fib` *any* value 
`n` (including *negative* values) and yet, `fib` must return 
values `b` such that `b >= n` *and* `n >= 0`. 

The latter requirement is a rather tall order when an arbitrary `n` 
is passed in as input --- `fib` can make no such guarantees since 
it was *given* the value `n` as a parameter. The only way `n` could 
be non-negative was that if the caller had sent in a non-negative value. 
Thus, we want to put the *burden of proof* on the right entity here, 
namely the caller.

To place the burden of proof appropriately, we just put the
non-negative refinement on the *input type*, like so

\begin{code}
{-@ fib' :: n:{v:Int | v >= 0} -> {b:Int | (n >= 0 && b >= n) } @-}
fib' :: Int -> Int
fib' 0 = 0
fib' 1 = 1
fib' n = fib (n-1) + fib (n-2)
\end{code}

where now at *calls to* `fib'` LiquidHaskell will check that the argument
is non-negative, and furthermore, when checking `fib'` LiquidHaskell will 
**assume** that the parameter `n` is indeed non-negative. So now the
constraint `n >= 0` on the output is somewhat redundant, and the
non-negative `n` guarantee holds trivially.

**Reason 2: The Specification is a Fib**

If you run the above in the demo, you will see that LiquidHaskell still
doth protest loudly, and frankly, one might start getting a little
frustrated at the stubbornness and petulance of the checker.

However, if you stare at the implementation, you will see that it in 
fact, *does not* meet the specification, as

~~~~~{.haskell}
fib' 2  == fib' 1 + fib' 0
        == 0 + 1
        == 1
~~~~~

LiquidHaskell is reluctant to prove things that are false. Rather than 
anthropomorphize, lets see why it is unhappy. 

Recall the somewhat simplified specification 

~~~~~{.haskell}
fib' :: n:Int -> { b:Int | (b >= n) } 
~~~~~

As we saw in the discussion about `abz`, at each recursive callsite
the *only information* LiquidHaskell uses about the returned value, 
is that described in the *output type* for that function call.
Thus, over here, LiquidHaskell reasons that the expression:

~~~~{.haskell}
fib (n-1) + fib (n-2)
~~~~

has the type

~~~~~{.haskell}
{b: Int | exists b1, b2. b  == b1 + b2 
                      && b1 >= n-1 
                      && b2 >= n-2     }
~~~~~

where the `b1` and `b2` denote the values returned by the 
recursive calls --- we get the above by plugging the parameters
`n-1` and `n-2` in for the parameter `n` in output type for `fib'`.
The SMT solver simplifies the above to

~~~~~{.haskell}
{b: Int | b >= 2n - 3}
~~~~~

and then, to check the output type, the LiquidHaskell checks 
the subtyping relation

~~~~~{.haskell}
{b: Int | b >= 2n - 3} <: {b: Int | b >= n}
~~~~~

which is **rejected** by the SMT solver as the implication

~~~~~{.haskell}
(b >= 2n - 2)  =>  (b >= n)
~~~~~

is *not valid* (e.g. when `n` is `2`) Thus, LiquidHaskell uses 
the SMT solver to deem `fib'` is indeed, **unsafe**.

**Fixing The Code**

How then, do we get Chris' spec to work out? It seems like it 
*should* hold (except for that pesky case where `n=2`. Indeed,
let's rig the code, so that all the base cases return `1`.

\begin{code}
{-@ fibOK :: n:Int -> {b:Int | ((b >= n) && (b >= 1))} @-}
fibOK :: Int -> Int
fibOK 0 = 1
fibOK 1 = 1
fibOK n = fibOK (n-1) + fibOK (n-2)
\end{code}

Here' we specify that not only is the output greater than the input, it is
**also** greater than `1`. Now in the recursive case, LiquidHaskell reasons
that the value being output is

~~~~~{.haskell}
{b: Int | exists b1, b2. b  == b1 + b2 
                      && b1 >= n-1 && b1 >= 1 
                      && b2 >= n-2 && b2 >= 1 }
~~~~~

which reduces to 

~~~~~{.haskell}
{b: Int | b = 2n - 3 && n >= 2 }
~~~~~

which, the SMT solver is happy to verifiy, is 
indeed a subtype of the specified output

~~~~~{.haskell}
{b: Int | b >= n && b >= 1 } 
~~~~~

Conclusion
----------

There are several things to take away. 

1. We need to distinguish between *assumptions* and *guarantees* 
   when writing specifications for functions.

2. For *modularity*, LiquidHaskell, like every type system, uses only
   the (refinement) *type*  of each function at each use site, and not the 
   function's *body*.

3. Some seemingly intuitive specifications often aren't; in future work it
   would be useful to actually [generate][mlton]  [tests][concolic] as 
   [counterexamples][icse04] that illustrate when a specification
   [fails][dsd].

[qblog101]: /blog/2013/01/01/refinement-types-101.lhs/#comment-772807850
[qreddit101]: http://www.reddit.com/r/haskell/comments/16w3hp/liquidhaskell_refinement_types_in_haskell_via_smt/c809160
[ref101]:  /blog/2013/01/01/refinement-types-101.lhs/ 
[concolic]: http://en.wikipedia.org/wiki/Concolic_testing
[icse04]: http://goto.ucsd.edu/~rjhala/papers/generating_tests_from_counterexamples.html
[dsd]: http://dl.acm.org/citation.cfm?doid=1348250.1348254
[mlton]: http://www.cs.purdue.edu/homes/zhu103/pubs/vmcai13.pdf

