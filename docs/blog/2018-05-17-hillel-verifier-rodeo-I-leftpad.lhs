---
layout: post
title: The Hillelogram Verifier Rodeo I (LeftPad) 
date: 2018-05-17
comments: true
author: Ranjit Jhala 
published: true
tags: reflection
demo: LeftPad.hs
---

<!--
<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">You have to provide a 100%, machine-checked guarantee that there are no problems with your code whatsoever. If it&#39;s so much easier to analyze FP programs than imperative programs, this should be simple, right?</p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432180837167104?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>
-->

A month ago, [Hillel Wayne](https://twitter.com/Hillelogram)
posted a [verification challenge](https://twitter.com/Hillelogram/status/987432180837167104)
comprising three problems that might _sound_ frivolous, 
but which, in fact, hit the sweet spot of being easy to 
describe and yet interesting to implement and verify. 
I had a lot of fun hacking them up in LH, and learned 
some things doing so.

Today, lets see how to implement the first 
of these challenges -- `leftPad` -- in Haskell, 
and to check Hillel's specification with LH. 

(Click here to [demo][demo])

<!-- more -->

<div class="hidden">
\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module PadLeft where 

import Prelude hiding (max, replicate, (++), (!!))
(!!) :: [a] -> Int -> a 
size :: [a] -> Int
(++) :: [a] -> [a] -> [a]
obviously         :: Int -> a -> [a] -> () 
replicate         :: Int -> a -> [a]
thmReplicate      :: Int -> a -> Int -> () 
thmAppLeft        :: [a] -> [a] -> Int -> ()
thmAppRight       :: [a] -> [a] -> Int -> ()
thmLeftPad        :: Int -> a -> [a] -> Int -> ()

{-@ reflect max @-}
max :: Int -> Int -> Int 
max x y = if x > y then x else y 

-- A ghost function only used in the specification
{-@ leftPadVal :: n:{Int | False} -> _ -> _ -> _ -> _ @-}
\end{code}
</div>

The LeftPad Challenge 
---------------------

The first of these problems was 
[leftPad](https://twitter.com/Hillelogram/status/987432181889994759)

<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">1. Leftpad. Takes a padding character, a string, and a total length, returns the string padded with that length with that character. If length is less than string, does nothing.<a href="https://t.co/X8qR8gTZdO">https://t.co/X8qR8gTZdO</a></p>&mdash; Hillel (@Hillelogram) <a href="https://twitter.com/Hillelogram/status/987432181889994759?ref_src=twsrc%5Etfw">April 20, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

Implementation 
--------------

First, lets write an idiomatic implementation 
of `leftPad` where we will take the liberty of 
generalizing 

- the **padding character** to be the input `c` that is of some (polymorphic) type `a` 
- the **string** to be the input `xs` that is a list of `a`

If the target length `n` is indeed greater than the input string `xs`, 
i.e. if `k = n - size xs` is positive, we `replicate` the character `c`
`k` times and append the result to the left of the input `xs`. 
Otherwise, if `k` is negative, we do nothing, i.e. return the input.

\begin{code}
{-@ reflect leftPad @-}
leftPad :: Int -> a -> [a] -> [a]
leftPad n c xs 
  | 0 < k     = replicate k c ++ xs 
  | otherwise = xs 
  where 
    k         = n - size xs
\end{code}

The code for `leftPad` is short because we've 
delegated much of the work to `size`, `replicate` 
and `++`. Here's how we can compute the `size` of a list:

\begin{code}
{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0 
size (x:xs) = 1 + size xs
\end{code}

and here is the list append function `++` :

\begin{code}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> 
            {v:[a] | size v = size xs + size ys} 
  @-}
[]     ++ ys = ys 
(x:xs) ++ ys = x : (xs ++ ys)
\end{code}

and finally the implementation of `replicate` :

\begin{code}
{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> 
                 {v:[a] | size v = n} 
  @-}
replicate 0 _ = [] 
replicate n c = c : replicate (n - 1) c
\end{code}

What shall we Prove? 
--------------------

My eyes roll whenever I read the phrase "proved X (a function, a program) _correct_".

There is no such thing as "correct".

There are only "specifications" or "properties", 
and proofs that ensures that your code matches 
those specifications or properties.

What _specifications_ shall we verify about our 
implementation of `leftPad`? One might argue that 
the above code is "obviously correct", i.e. the 
implementation more or less directly matches the 
informal requirements. 

One way to formalize this notion of "obviously correct" 
is to verify a specification that directly captures 
the informal requirements: 

\begin{code}
{-@ obviously :: n:Int -> c:a -> xs:[a] -> 
      { leftPad n c xs = if (size xs < n) 
                         then (replicate (n - size xs) c ++ xs) 
                         else xs } 
  @-}
obviously _ _ _ = () 
\end{code}

In the above, the type signature is a specification 
that says that for all `n`, `c` and `xs`, the value 
returned by `leftPad n c xs` is `xs` when `n` is 
too small, and the suitably padded definition otherwise. 

The code, namely `()`, is the proof. 
LH is able to trivially check that `leftPad` 
meets the "obviously correct" specification, 
because, well, in this case, the implementation 
_is_ the specification. (Incidentally, this 
is also why the [Idris solution][idris-leftpad] 
is terse.)

So, if you are happy with the above specification, 
you can stop reading right here: we're done. 

Hillel's Specifications 
-----------------------

However, the verification rodeo is made more 
interesting by Hillel's [Dafny specifications][dafny-leftpad]:

1. **Size** The `size` of the returned sequence is the 
   larger of `n` and the size of `xs`;

2. **Pad-Value** Let `K = n - size xs`. We require 
   that the `i`-th element of the padded-sequence 
   is `c` if `0 <= i < K`, and is the `i - K`-th 
   element of `xs` otherwise.

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/leftpad-spec.png"
       alt="Ribbons" height="150">
  </div>
</div>


Digression: The Importance of being Decidable 
---------------------------------------------

LH, like many of the other rodeo entries, uses 
SMT solvers to automate verification. For example, 
the `leftPad` solutions in [Dafny][dafny-leftpad] 
and [SPARK][spark-leftpad] and [F*][fstar-leftpad] 
make heavy use [quantified axioms to encode properties 
of sequences.][dafny-seq-axioms] 

However, unlike its many SMT-based brethren, LH 
takes a somewhat fanatical stance: it _never_ uses 
quantifiers or axioms. We take this rigid position
because SMT solvers are only _predictable_ on 
queries from (certain) **decidable logics**.
Axioms, or more generally, quantified formulas 
rapidly take SMT solvers out of this "comfort zone",
causing them to reject valid formulas, run slowly, 
or even, [to run forever][regehr-tweet].

<!--
<blockquote class="twitter-tweet" data-lang="en"><p lang="en" dir="ltr">I mean, I&#39;m somewhat kind of serious here, I think unneeded generality makes things really difficult often. as a random example quantifiers seem to throw z3 into a really bad place, even when they&#39;re easy ones.</p>&mdash; John Regehr (@johnregehr) <a href="https://twitter.com/johnregehr/status/996901816842440704?ref_src=twsrc%5Etfw">May 16, 2018</a></blockquote>
<script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/regehr-tweet-quantifiers.png"
       alt="Ribbons" height="100">
  </div>
</div>
-->

Thus, we have chosen to deliberately avoid 
the siren song of quantifiers by lashing LH 
firmly to the steady mast of decidable logics.

Reasoning about Sequences 
-------------------------

Unfortunately, this design choice leaves us 
with some work: we must develop i.e. _state_ 
and _prove_ relevant properties about sequences 
from scratch.

**Indexing into a Sequence**

To start, lets define the notion of the `i`-th element of 
a sequence (this is pretty much Haskell's list-index operator)

\begin{code}
{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(x:_)  !! 0 = x 
(_:xs) !! n = xs !! (n - 1)
\end{code}

**Replicated Sequences** 

Next, we verify that _every_ element in a `replicate`-d 
sequence is the element being cloned:

\begin{code}
{-@ thmReplicate :: n:Nat -> c:a -> i:{Nat | i < n} -> 
                    { replicate n c !! i  == c } 
  @-}
thmReplicate n c i 
  | i == 0    = ()
  | otherwise = thmReplicate (n - 1) c (i - 1) 
\end{code}

LH verifies the above "proof by induction": 

- In the base case `i == 0` and the value returned is `c` 
  by the definition of `replicate` and `!!`. 
  
- In the inductive case, `replicate n c !! i` is equal to 
  `replicate (n-1) c !! (i-1)` which, by the "induction hypothesis" 
  (i.e. by recursively calling the theorem) is `c`.

**Concatenating Sequences** 

Finally, we need two properties that relate 
concatenation and appending, namely, the 
`i`-th element of `xs ++ ys` is: 

- **Left** the `i`-th element of `xs` if `0 <= i < size xs`, and 
- **Right** the `i - size xs` element of `ys` otherwise.

\begin{code}
{-@ thmAppLeft :: xs:[a] -> ys:[a] -> {i:Nat | i < size xs} -> 
                  { (xs ++ ys) !! i == xs !! i } 
  @-} 
thmAppLeft (x:xs) ys 0 = () 
thmAppLeft (x:xs) ys i = thmAppLeft xs ys (i-1)      

{-@ thmAppRight :: xs:[a] -> ys:[a] -> {i:Nat | size xs <= i} -> 
                   { (xs ++ ys) !! i == ys !! (i - size xs) } 
  @-} 
thmAppRight []     ys i = () 
thmAppRight (x:xs) ys i = thmAppRight xs ys (i-1)      
\end{code}

Both of the above properties are proved by induction on `i`.

Proving Hillel's Specifications 
-------------------------------

Finally, we're ready to state and prove Hillel's specifications. 

**Size Specification**

The size specification is straightforward, in that LH proves 
it automatically, when type-checking `leftPad` against the 
signature:

\begin{code}
{-@ leftPad :: n:Int -> c:a -> xs:[a] -> 
                {res:[a] | size res = max n (size xs)} 
  @-}
\end{code}

**Pad-Value Specification**

We _specify_ the pad-value property -- i.e. the `i`-th 
element equals `c` or the corresponding element of `xs` -- 
by a type signature:

\begin{code}
{-@ thmLeftPad 
      :: n:_ -> c:_ -> xs:{size xs < n} -> i:{Nat | i < n} ->
         { leftPad n c xs !! i ==  leftPadVal n c xs i }                               
  @-}

{-@ reflect leftPadVal @-}
leftPadVal n c xs i 
  | i < k     = c 
  | otherwise = xs !! (i - k)
  where k     = n - size xs 
\end{code}

**Pad-Value Verification**

We _verify_ the above property by filling in the 
implementation of `thmLeftPad` as:

\begin{code}
thmLeftPad n c xs i 
  | i < k     = thmAppLeft  cs xs i `seq` thmReplicate k c i   
  | otherwise = thmAppRight cs xs i
  where 
    k         = n - size xs 
    cs        = replicate k c
\end{code}

The "proof"  -- in quotes because its 
just a Haskell function -- simply combines 
the replicate- and concatenate-left theorems 
if `i` is in the "pad", and the concatenate-right 
theorem, otherwise.

Conclusions 
-----------

That concludes part I of the rodeo. What did I learn from this exercise?

1. Even apparently simple functions like `leftPad` can 
   have _many_ different specifications; there is no 
   necessarily "best" specification as different specs 
   make different assumptions about what is "trusted", 
   and more importantly, though we didn't see it here, 
   ultimately a spec is a particular _view_ into how a 
   piece of code behaves and 
   we may want different views depending on the context where we want 
   to use the given piece of code.

2. The `leftPad` exercise illustrates a fundamental 
   problem with Floyd-Hoare style "modular" verification, 
   where pre- and post-conditions (or contracts or refinement 
   types or ...) are used to modularly "abstract" functions 
   i.e. are used to describe the behavior of a function 
   at a call-site. As the above exercise shows, we often 
   need properties connecting the behavior of different 
   functions, e.g. append (`++`), indexing (`!!`). 
   In these cases, the only meaningful _specification_ 
   for the underlying function _is its implementation_.

3. Finally, the above proofs are all over user-defined 
   recursive functions which this was not even possible 
   before [refinement reflection][tag-reflection], i.e 
   till about a year ago. I'm also quite pleased by how 
   [logical evaluation][tag-ple] makes these proofs 
   quite short, letting LH verify expressive specifications 
   while steering clear of the siren song of quantifiers.

[demo]:             http://goto.ucsd.edu:8090/index.html#?demo=LeftPad.hs
[dafny-leftpad]:    https://rise4fun.com/Dafny/nbNTl
[spark-leftpad]:    https://blog.adacore.com/taking-on-a-challenge-in-spark
[fstar-leftpad]:    https://gist.github.com/graydon/901f98049d05db65d9a50f741c7f7626
[idris-leftpad]:    https://github.com/hwayne/lets-prove-leftpad/blob/master/idris/Leftpad.idr
[dafny-seq-axioms]: https://github.com/Microsoft/dafny/blob/master/Binaries/DafnyPrelude.bpl#L898-L1110
[tag-reflection]:   /tags/reflection.html
[tag-ple]:          /tags/ple.html
[regehr-tweet]:     https://twitter.com/johnregehr/status/996901816842440704
