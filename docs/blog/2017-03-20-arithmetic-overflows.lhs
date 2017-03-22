---
layout: post
title: Arithmetic Overflows
date: 2017-03-20
author: Ranjit Jhala
published: true
comments: true
tags: basic
demo: overflow.hs
---


Computers are great at crunching numbers.
However, if programmers aren't careful, their
machines can end up biting off more than
they can chew: simple arithmetic operations
over very large (or very tiny) inputs can
*overflow* leading to bizarre crashes
or vulnerabilities. For example,
[Joshua Bloch's classic post][bloch]
argues that nearly all binary searches
are broken due to integer overflows.
Lets see how we can teach LiquidHaskell
to spot such overflows.

<!-- more -->

<div class="hidden">
\begin{code}
module Bounded where

import           Control.Exception (assert)
import           Prelude hiding (Num (..))
import qualified Prelude

plusStrict :: Int -> Int -> Int
plusLazy   :: Int -> Int -> Int
mono       :: Int -> Bool
\end{code}
</div>

1. The Problem
--------------


LiquidHaskell, like some programmers, likes to make believe
that `Int` represents the set of integers. For example, you
might define a function `plus` as:

\begin{code}
{-@ plus :: x:Int -> y:Int -> {v:Int | v == x + y} @-}
plus :: Int -> Int -> Int
plus x y = x Prelude.+ y
\end{code}

The output type of the function states that the returned value
is equal to the \emph{logical} result of adding the two inputs.

The above signature lets us "prove" facts like addition by one
yields a bigger number:

\begin{code}
{-@ monoPlus :: Int -> {v:Bool | v <=> true } @-}
monoPlus :: Int -> Bool
monoPlus x = x < plus x 1
\end{code}

Unfortunately, the signature for plus and hence, the above
"fact" are both lies.

LH _checks_ `plus` as the same signature is _assumed_
for the primitive `Int` addition operator `Prelude.+`.
LH has to assume _some_ signature for this "foreign"
machine operation, and by default, LH assumes that
machine addition behaves like logical addition.

However, this assumption, and its consequences are
only true upto a point:

```haskell
λ>  monoPlus 0
True
λ>  monoPlus 100
True
λ>  monoPlus 10000
True
λ>  monoPlus 1000000
True
```

Once we get to `maxBound` at the very edge of `Int`,
a tiny bump is enough to send us tumbling backwards
into a twilight zone.

```haskell
λ> monoPlus maxBound
False

λ> plus maxBound 1
-9223372036854775808
```

2. Keeping Int In Their Place
-----------------------------

The news isn't all bad: the glass half full
view is that for "reasonable" values
like 10, 100, 10000 and 1000000, the
machine's arithmetic _is_ the same as
logical arithmetic. Lets see how to impart
this wisdom to LH. We do this in two steps:
define the *biggest* `Int` value, and then,
use this value to type the arithmetic operations.

**A. The Biggest Int**

First, we need a way to talk about
"the edge" -- i.e. the largest `Int`
value at which overflows occur.

We could use the concrete number

```haskell
λ> maxBound :: Int
9223372036854775807
```

However, instead of hardwiring a particular number,
a more general strategy is to define a symbolic
constant `maxInt` to represent _any_ arbitrary
overflow value and thus, make the type checking
robust to different machine integer widths.

\begin{code}
-- defines an Int constant called `maxInt`
{-@ measure maxInt :: Int @-}
\end{code}

To tell LH that `maxInt` is the "biggest" `Int`,
we write a predicate that describes values bounded
by `maxInt`:

\begin{code}
{-@ predicate Bounded N = 0 < N + maxInt && N < maxInt @-}
\end{code}

Thus, `Bounded n` means that the number `n` is in
the range `[-maxInt, maxInt]`.

**B.  Bounded Machine Arithmetic**

Next, we can assign the machine arithmetic operations
types that properly capture the possibility of arithmetic
overflows. Here are _two_ possible specifications.

**Strict: Thou Shalt Not Overflow** A _strict_ specification
simply prohibits any overflow:

\begin{code}
{-@ plusStrict :: x:Int -> y:{Int|Bounded(x+y)} -> {v:Int|v = x+y} @-}
plusStrict x y = x Prelude.+ y
\end{code}

The inputs `x` and `y` _must_ be such that the result is `Bounded`,
and in that case, the output value is indeed their logical sum.

**Lazy: Overflow at Thine Own Risk** Instead, a _lazy_
specification could permit overflows but gives no
guarantees about the output when they occur.

\begin{code}
{-@ plusLazy :: x:Int -> y:Int -> {v:Int|Bounded(x+y) => v = x+y} @-}
plusLazy x y = x Prelude.+ y
\end{code}

The lazy specification says that while `plusLazy`
can be called with any values you like, the
result is the logical sum
*only if there is no overflow*.


To understand the difference between the two
specifications, lets revisit the `monoPlus`
property using the new machine-arithmetic
sensitive signatures:

\begin{code}
{-@ monoPlusStrict :: Int -> {v:Bool | v <=> true } @-}
monoPlusStrict x = x < plusStrict x 1

{-@ monoPlusLazy :: Int -> {v:Bool | v <=> true } @-}
monoPlusLazy x = x < plusLazy x 1
\end{code}

Both are rejected by LH, since, as we saw earlier,
the functions _do not_ always evaluate to `True`.
However, in the strict version the error is at the
possibly overflowing call to `plusStrict`.
In the lazy version, the call to `plusLazy` is
accepted, but as the returned value is some
arbitrary `Int` (not the logical `x+1`), the
comparison may return `False` hence the output
is not always `True`.

**Exercise:** Can you fix the specification
for `monoPlusStrict` and `monoPlusLazy` to
get LH to verify the implementation?


3. A Typeclass for Machine Arithmetic
-------------------------------------

Its a bit inconvenient to write `plusStrict` and `plusLazy`,
and really, we'd just like to write `+` and `-` and so on.
We can do so, by tucking the above specifications into
a _bounded numeric_ typeclass whose signatures capture machine
arithmetic. First, we define a `BoundedNum` variant of `Num`

\begin{code}
class BoundedNum a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  -- other operations ...
\end{code}

and now, we can define its `Int` instance just as wrappers
around the `Prelude` operations:

\begin{code}
instance BoundedNum Int where
  x + y = x Prelude.+ y
  x - y = x Prelude.- y
\end{code}

Finally, we can tell LH that the above above instance obeys the
(strict) specifications for machine arithmetic:

\begin{code}
{-@ instance BoundedNum Int where
      + :: x:Int -> y:{Int | Bounded (x+y)} -> {v:Int | v == x+y };
      - :: x:Int -> y:{Int | Bounded (x-y)} -> {v:Int | v == x-y }
  @-}
\end{code}

With the above instance in scope, we can just use the plain `+`
operator and have LH flag potential overflows:

\begin{code}
{-@ mono :: Int -> {v:Bool | v <=> true} @-}
mono x = x < x + 1
\end{code}


4. An Application: Binary Search
--------------------------------

The above seems a bit paranoid. Do overflows _really_ matter?
And if they do, is it really practical to check for them using
the above?

[Joshua Bloch's][bloch] famous article describes a
tricky overflow bug in an implementation of binary-search
that lay hidden in plain sight in classic textbooks and his
own implementation in the JDK for nearly a decade.
Gabriel Gonzalez wrote a lovely [introduction to LH][lh-gonzalez]
using binary-search as an example, and a careful reader
[pointed out][lh-overflow-reddit] that it had the same
overflow bug!

Lets see how we might spot and fix such bugs using `BoundedNum`.

<div class="row">
<div class="col-md-4">
**A. Off by One** Lets begin by just using
the default `Num Int` which ignores overflow.
As Gabriel explains, LH flags a bunch of errors
if we start the search with `loop x v 0 n` as
the resulting search can access `v` at any
index between `0` and `n` inclusive, which
may lead to an out of bounds at `n`.
We can fix the off-by-one by correcting the
upper bound to `n-1`, at which point LH
reports the code free of errors.
</div>

<div class="col-md-8">
<img id="splash-binarySearch-A"
     class="center-block anim"
     png="/liquidhaskell-blog/static/img/splash-binarySearch-A.png"
     src="/liquidhaskell-blog/static/img/splash-binarySearch-A.png">
</div>
</div>

<br>


<div class="row">
<div class="col-md-8">
<img id="splash-binarySearch-B"
     class="center-block anim"
     png="/liquidhaskell-blog/static/img/splash-binarySearch-B.png"
     src="/liquidhaskell-blog/static/img/splash-binarySearch-B.png">
</div>

<div class="col-md-4">
**B. Lots of Overflows** To spot arithmetic overflows, we need
only hide the default `Prelude` and instead import the `BoundedNum`
instance described above. Upon doing so, LH flags a whole bunch of
potential errors -- essentially *all* the arithmetic operations which
seems rather dire!
</div>
</div>


<div class="row">
<div class="col-md-4">
**C. Vector Sizes are Bounded** Of course, things
aren't _so_ bad. LH is missing the information that
the size of any `Vector` must be `Bounded`. Once we
inform LH about this invariant with the
[`using` directive][lh-invariants], it infers that
as the `lo` and `hi` indices are upper-bounded by
the `Vector`'s size, all the arithmetic on them is
also `Bounded` and hence, free of overflows.
</div>

<div class="col-md-8">
<img id="splash-binarySearch-C"
     class="center-block anim"
     png="/liquidhaskell-blog/static/img/splash-binarySearch-C.png"
     src="/liquidhaskell-blog/static/img/splash-binarySearch-C.png">
</div>
</div>

<br>

<div class="row">
<div class="col-md-8">
<img id="splash-binarySearch-D"
     class="center-block anim"
     png="/liquidhaskell-blog/static/img/splash-binarySearch-D.png"
     src="/liquidhaskell-blog/static/img/splash-binarySearch-D.png">
</div>

<div class="col-md-4">
**D. Staying In The Middle**
Well, *almost* all. The one pesky pink highlight that
remains is exactly the bug that Bloch made famous. Namely:
the addition used to compute the new midpoint between `lo`
and `hi` could overflow e.g. if the array was large and both
those indices were near the end. To ensure the machine doesn't
choke, we follow Bloch's suggestion and re-jigger the computation
to instead compute the midpoint by splitting the difference
between `hi` and `lo`! the code is now free of arithmetic
overflows and truly memory safe.
</div>
</div>


[lh-invariants]: https://github.com/ucsd-progsys/liquidhaskell/blob/develop/README.md#invariants
[lh-gonzalez]: http://www.haskellforall.com/2015/12/compile-time-memory-safety-using-liquid.html
[bloch]: https://research.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html
[lh-overflow-reddit]: https://www.reddit.com/r/haskell/comments/3ysh9k/haskell_for_all_compiletime_memory_safety_using/cyg8g60/
