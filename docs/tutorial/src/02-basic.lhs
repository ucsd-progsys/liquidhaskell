
Refinement Types
================



\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
module Intro where

import Prelude hiding                   (abs)
import Language.Haskell.Liquid.Prelude  (liquidAssert)
\end{code}


What is a Refinement Type?
--------------------------

In a nutshell, 

$$\mbox{Refinement Types} = \mbox{Types} + \mbox{Logical Predicates}$$

That is, refinement types allow us to decorate types with 
*logical predicates*, which you can think of as *boolean-valued*
Haskell expressions, that constrain the set of values described
by the type. This lets you specify sophisticated invariants of
the underlying values. 

Let us define some refinement types:

\begin{code}
{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}
\end{code}

ASIDE The binder `v` is called the *value variable*.
Hence, `Zero` describes the *set of* `Int` values that are equal to `0`,
that is, the singleton set containing just `0`, and `NonZero` describes
the set of `Int` values that are *not* equal to `0`, that is, the set
`..., -2, -1, 1, 2, ...`.

**Note:** We will use `@`-marked comments to write refinement type 
annotations the Haskell source file, making these types, quite literally,
machine-checked comments!

Lets use these types! We can write:

\begin{code}
{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ one, two, three :: NonZero @-}
one   = 1 :: Int
two   = 2 :: Int
three = 3 :: Int
\end{code}

and so on. Of course, LH will grumble if we try to say nonsensical things like:

\begin{code}
{-@ one' :: Zero @-}
one' = 1 :: Int
\end{code}

Lets look at the error message:

\begin{verbatim}
 02-basic.lhs:58:8: Error: Liquid Type Mismatch
   Inferred type
     VV : Int | VV == (1  :  int)
  
   not a subtype of Required type
     VV : Int | VV == 0
 \end{verbatim}

The message says that the expression `1 :: Int` has the type `{v:Int | v == 1}` which
is *not* (a subtype of) the *required* type `{v:Int | v == 0}`, as indeed the value `1`
is not equal to `0`.

Subtyping
---------

What is this business of *subtyping*?

Suppose we have some more refinements of `Int` 

\begin{code}
{-@ type Nat  = {v:Int | 0 <= v}        @-}
{-@ type Even = {v:Int | v mod 2 == 0 } @-}
\end{code}

What is the *right* type for `zero`?

It can be `Zero` of course, as we saw above, but also `Nat`:

\begin{code}
{-@ zero' :: Nat @-}
zero'     = zero 
\end{code}

and also `Even`

\begin{code}
{-@ zero'' :: Even @-}
zero''     = zero 
\end{code}

and also any other satisfactory refinement


\begin{code}
{-@ type Lt100 = {v:Int | v < 100} @-}

{-@ zero''' :: Lt100  @-}
zero'''     = zero 
\end{code}

(Aside: we use a different names `zero'`, `zero''` etc. for a silly technical 
reason -- LiquidHaskell requires that we ascribe a single refinement type to 
a top-level name.)


How does this work? Well, `Zero` which is the *most precise type* for `0::Int`
is a *subtype* of `Nat` and `Even` and `{v:Int | v < 100}`. Intuitively, this
is because intuitively, the set of values defined by `Zero` is a *subset* of
the values defined by `Nat`, `Even` and `Lt100`, because logically,

+ $$v = 0 \Rightarrow 0 \leq v$$
+ $$v = 0 \Rightarrow v mod 2 == 0$$
+ $$v = 0 \Rightarrow v < 100 $$

In general, we can *combine* multiple refinements (as long as all of them hold of course!)

\begin{code}
{-@ zero''' :: {v: Int | 0 <= v &&  v mod 2 == 0 && v < 100 } @-}
zero'''' :: Int
zero'''' = 0
\end{code}

Finally, we could write a single type that captures all the properties above:

\begin{code}
{-@ zero_ :: {v: Int | 0 <= v && (v mod 2 = 0) && v < 100} @-}
zero_     =  0 :: Int
\end{code}

The key points are:

1. A refinement type is just a type *decorated* with logical predicates.
2. A value can have *different* refinement types that describe different properties.
3. If we *erase* the logical predicates we get back *exactly* the usual Haskell types that we know and love.
4. A vanilla Haskell type, say `Int` has the trivial refinement `true` i.e. is really `{v: Int | true}`.

Writing Specifications
----------------------

Next, lets use refinement types to write more interesting specifications.

First, we can write a wrapper around the usual `error` function 

\begin{code}
{-@ die :: {v: String | false } -> a  @-}
die     :: String -> a
die     = error
\end{code}

The interesting thing about the type signature for `error'` is that the
input type has the refinement `false`. That is, the function must only be
called with `String`s that satisfy the predicate `false`.

Huh? Of course, there are *no* such values!

Indeed! Thus, a program containing `die` typechecks *only* when LiquidHaskell
can prove that `die` is *never called*. For example, LH will *accept*

\begin{code}
cantDie = if 1 + 1 == 3
            then die "horrible death"
            else ()
\end{code}

because it reasons that the branch is always `False` and so `die` cannot be called,
but will *reject* 

\begin{code}
canDie = if 1 + 1 == 2
           then die "horrible death"
           else ()
\end{code}

because of course, the branch may (will!) be `True` and so `die` can be called.




Refining Function Types : Preconditions
---------------------------------------

Lets use the above to write a *divide* function that *only accepts* non-zero
denominators. 

\begin{code}
divide'     :: Int -> Int -> Int
divide' n 0 = die "divide by zero"
divide' n d = n `div` d
\end{code}

From the above, it is pretty clear that `div` is only called with non-zero
divisor's *but* we have just swept the problem from one place to another; LH
reports an error at the call to `"die"` because of course, what if `divide'`
is actually invoked with a `0` divisor?

We can specify that will not happen, with a *precondition* that says that
the second argument is non-zero.

and now write a proper and safe:

\begin{code}
{-@ divide :: Int -> NonZero -> Int @-}
divide     :: Int -> Int -> Int
divide n 0 = die "divide by zero"
divide n d = n `div` d
\end{code}

How *does* LH verify the above function? 

The key step is that LH deduces that the expression `"divide by zero"`
is not merely of type `String`, but in fact has the the refined type
`{v:String | false}` *in the context* in which the call to `die'` occurs.

LH arrives at this conclusion by using the fact that in the first
equation for `divide` the *denominator* parameter is in fact

\begin{verbatim}
0 :: {v: Int | v == 0}
\end{verbatim}

which *contradicts* the precondition (i.e. input) type.

Thus, by contradition, LH deduces that the first equation is
*dead code* and hence `die` will not be called at run-time.

Of course, this requires that when we *use* `divide` we only
supply provably non-zero arguments, so:

\begin{code}
avg2 x y   = divide (x + y) 2

avg3 x y z = divide (x + y + z) 3
\end{code}

are just fine.

**Exercise** Consider the general list-averaging function below.

\begin{code}
avg       :: [Int] -> Int
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs
\end{code}

1. Why does LH flag an error at `n` ?
2. How can you modify the code so LH verifies it?


Refining Function Types : Postconditions
----------------------------------------

Next, lets see how we can use refinements to describe the *outputs* of a
function. Consider the following simple *absolute value* function

\begin{code}
abs           :: Int -> Int
abs n
  | 0 < n     = n
  | otherwise = 0 - n
\end{code}

We can use a refinement on the output type to specify that the function 
returns non-negative values

\begin{code}
{-@ abs :: Int -> Nat @-}
\end{code}

LH *verifies* that `abs` indeed enjoys the above type by
deducing that `n` is trivially non-negative when `0 < n` and that in 
the `otherwise` case, i.e. when `not (0 < n)` the value `0 - n` is
indeed non-negative (lets not worry about underflows for the moment.)

LH is able to automatically make these arithmetic deductions
by using an [SMT solver](http://en.wikipedia.org/wiki/Satisfiability_Modulo_Theories)
which has decision built-in procedures for arithmetic, to reason about
the logical refinements.


Testing Values: Booleans and Propositions
-----------------------------------------

In the above example, we *compute* a value that is guaranteed to be a `Nat`.

What if instead, we wish to *test* if a value satisfies some property, say, is `NonZero` ?

Suppose we want to write a command-line "calculator" that takes two numbers and divides them.

\begin{code}
repl = do putStrLn "Enter numerator"
          n <- readLn :: IO Int
          putStrLn "Enter denominator"
          d <- readLn :: IO Int
          putStrLn (result n d)
          repl 
\end{code}

The `result` function checks if `d` is strictly positive (and hence, non-zero), and does
the division, or otherwise complains to the user.

\begin{code}
result n d
  | isPositive d = "Result = " ++ show (n `divide` d) 
  | otherwise    = "Humph, please enter positive denominator!"
\end{code}

`isPositive` is a simple test that returns a `True` if its input is strictly greater than `0`
or `False` otherwise:

\begin{code}
isPositive :: Int -> Bool
isPositive x = x > 0
\end{code}

We type it as:

\begin{code}
{-@ isPositive :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
\end{code}

Read `Prop v` as `v` is equal to `True`, and  `not (Prop v)` as `v` is equal to `False`.

That is, the output type (postcondition) states that `isPositive x` returns `True` if and only if
`x` was in fact strictly greater than `0`. In this way, we can *test* raw values that are read from
the user to establish that they satistfy some property (here, `Pos` and hence `NonZero`) in order
to safely perform some computation on it.

**Exercise**

+ What if you DELETE the spec for isPositive ?

+ How can you CHANGE the spec for isPositive while preserving safety?


**Exercise** Consider the following [assert](https://www.haskell.org/hoogle/?hoogle=assert) function

\begin{code}
{-@ lAssert  :: Bool -> a -> a @-}
lAssert True  x = x
lAssert False _ = die "yikes, assert failure!" 
\end{code}

We can use the function as follows:

\begin{code}
yes :: ()
yes = lAssert (1 + 1 == 2) ()

no :: ()
no = lAssert (1 + 1 == 3) ()
\end{code}

Add suitable refinements in the type for `lAssert` so that:

1. `lAssert` is accepted,
2. `yes` is accepted, but,
3. `no` is rejected.

**Hint** How will you specify a precondition that `lAssert` is only called with `True`?


Putting It All Together
-----------------------

Lets wrap up this introduction with a simple `truncate` function 
that connects all the dots. 

\begin{code}
truncate :: Int -> Int -> Int
truncate i max  
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where
      i'       = abs i
      max'     = abs max 
\end{code}

`truncate i n` simply returns `i` if its absolute value is less the
upper bound `max`, and otherwise *truncates* the value at the maximum.
LH verifies that the use of `divide` is safe by inferring that 
at the call site

1. `i' > max'` from the branch condition.
2. `0 <= i'`   from the `abs` postcondition (click on `i'`).
3. `0 <= max'` from the `abs` postcondition (click on `max'`).

From the above, LH infers that `i' /= 0`. That is, at the
call site `i' :: NonZero`, thereby satisfying the precondition
for `divide` and verifying that the program has no pesky
divide-by-zero errors.

**Conclusion**

This concludes our quick introduction to Refinement Types and
LiquidHaskell. Hopefully you have some sense of how to 

1. **Specify** fine-grained properties of values by decorating their
   types with logical predicates.
2. **Encode** assertions, preconditions, and postconditions with suitable
   function types.
3. **Verify** semantic properties of code by using automatic logic engines 
   (SMT solvers) to track and establish the key relationships between 
   program values.

