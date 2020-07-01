# Writing Specifications


Modules WITHOUT code
--------------------

When checking a file `target.hs`, you can specify an _include_ directory by

    liquid -i /path/to/include/  target.hs

Now, to write specifications for some **external module** `Foo.Bar.Baz` for which
you **do not have the code**, you can create a `.spec` file at:

    /path/to/include/Foo/Bar/Baz.spec

See, for example, the contents of

+ [include/Prelude.spec](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Prelude.spec)
+ [include/Data/List.spec](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/List.spec)
+ [include/Data/Vector.spec](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec)

**Note**:

+ The above directories are part of the LH prelude, and included by
  default when running `liquid`.
+ The `.spec` mechanism is *only for external modules** without code,
  see below for standalone specifications for **internal** or **home** modules.


Modules WITH code: Data
-----------------------

Write the specification directly into the .hs or .lhs file,
above the data definition. See, for example, [tests/pos/Map.hs](tests/pos/Map.hs)

    {-@
    data Map k a <l :: k -> k -> Prop, r :: k -> k -> Prop>
      = Tip
      | Bin (sz    :: Size)
            (key   :: k)
            (value :: a)
            (left  :: Map <l, r> (k <l key>) a)
            (right :: Map <l, r> (k <r key>) a)
    @-}
    data Map k a = Tip
                 | Bin Size k a (Map k a) (Map k a)

You can also write invariants for data type definitions
together with the types. For example, see [tests/pos/record0.hs](tests/pos/record0.hs)

    {-@ data LL a = BXYZ { size  :: {v: Int | v > 0 }
                         , elems :: {v: [a] | (len v) = size }
                         }
    @-}

Finally you can specify the variance of type variables for data types.
For example, see [tests/pos/Variance.hs](tests/pos/Variance.hs), where data type `Foo` has four
type variables `a`, `b`, `c`, `d`, specified as invariant, bivariant,
covariant and contravariant, respectively.

    data Foo a b c d
    {-@ data variance Foo invariant bivariant covariant contravariant @-}


Modules WITH code: Functions
----------------------------

Write the specification directly into the .hs or .lhs file,
above the function definition. [For example](tests/pos/spec0.hs)

    {-@ incr :: x:{v: Int | v > 0} -> {v: Int | v > x} @-}
    incr   :: Int -> Int
    incr x = x + 1

Modules WITH code: Type Classes
-------------------------------

Write the specification directly into the .hs or .lhs file,
above the type class definition. [For example](tests/pos/Class.hs)

    {-@ class Sized s where
          size :: forall a. x:s a -> {v:Int | v = (size x)}
    @-}
    class Sized s where
      size :: s a -> Int

Any measures used in the refined class definition will need to be
*generic* (see [Specifying Measures](#specifying-measures)).


As an alternative, you can refine class instances.
[For example](tests/classes/pos/Inst00.hs)

~~~~
instance Compare Int where

{-@ instance Compare Int where
    cmax :: Odd -> Odd -> Odd
  @-}

cmax y x = if x >= y then x else y
~~~~

When `cmax` method is used on `Int`, liquidHaskell will give it
the refined type `Odd -> Odd -> Odd`.

Note that currently liquidHaskell does not allow refining instances of
refined classes.

Modules WITH code: QuasiQuotation
---------------------------------

Instead of writing both a Haskell type signature *and* a
LiquidHaskell specification for a function, the `lq`
quasiquoter in the `LiquidHaskell` module can be used
to generate both from just the LiquidHaskell specification.

```haskell
module Nats (nats) where

{-@ nats :: [{v:Int | 0 <= v}] @-}
nats :: [Int]
nats = [1,2,3]
```

can be written as

```haskell
{-# LANGUAGE QuasiQuotes #-}
module Nats (nats) where

import LiquidHaskell

[lq| nats :: [{v:Int | 0 <= v}] |]
nats = [1,2,3]
```

and the `lq` quasiquoter will generate the plain `nats :: [Int]` when GHC
compiles the module.

Refined type aliases (see the next section) can also be written inside `lq`; for
example:

```haskell
{-# LANGUAGE QuasiQuoters #-}
module Nats (Nat, nats) where

[lq| type Nat = {v:Int | 0 <= v} |]

[lq| nats :: [Nat] |]
nats = [1,2,3]
```

Here, the `lq` quasiquoter will generate a plain Haskell
type synonym for `Nat` as well as the refined one.

Note that this is still an experimental feature, and
currently requires that one depend on LiquidHaskell
as a build dependency for your project; the quasiquoter
will be split out eventually into an independent,
dependency-light package. Also, at this time, writing
a type inside `lq` which refers to a refined type alias
for which there is not a plain Haskell type synonym of the
same name will result in a "not in scope" error from GHC.

Standalone Specifications for Internal Modules
----------------------------------------------

Recall that the `.spec` mechanism is only for modules whose
code is absent; if code is present then there can be multiple,
possibly conflicting specifications. Nevertheless, you may want,
for one reason or another, to write (assumed) specifications
outside the file implementing the module.

You can do this as follows.

`Lib.hs`

```haskell
module Lib (foo) where

foo a = a
```

now, instead of a `.spec` file, just use a haskell module, e.g. `LibSpec.hs`

```haskell
module LibSpec ( module Lib ) where

import Lib

-- Don't forget to qualify the name!

{-@ Lib.foo :: {v:a | false} -> a @-}
```

and then here's `Client.hs`

```haskell
module Client where

import Lib      -- use this if you DON'T want the spec
import LibSpec  -- use this if you DO want the spec, in addition to OR instead of the previous import.

bar = foo 1     -- if you `import LibSpec` then this call is rejected by LH
```

Inductive Predicates
--------------------

**Very Experimental**

LH recently added support for *Inductive Predicates*
in the style of Isabelle, Coq etc. These are encoded
simply as plain Haskell GADTs but suitably refined.

Apologies for the minimal documentation; see the
following examples for details:

* [Even and Odd](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/ple/pos/IndEven.hs)
* [Permutations](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/ple/pos/IndPerm.hs)
* [Transitive Closure](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/ple/pos/IndStar.hs)
* [RegExp Derivatives](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/ple/pos/RegexpDerivative.hs)
* [Type Safety of STLC](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/ple/pos/STLC2.hs)

Implicit Arguments
------------------

**Experimental**

There is experimental support for implicit arguments, solved for with congruence closure. For example, consider [Implicit1.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/pos/Implicit1.hs):

```haskell
{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+1} @-}
foo f = 1 + f ()

{-@ test1 :: IntN 11 @-}
test1 = foo (\_ -> 10)
```

Here, the refinement on `(\_ -> 10) :: Int -> { v:Int | v = 10 }` allows us to solve for `n = 10`, the implicit argument to `foo`.


Refinement Type Aliases
-----------------------

#### Predicate Aliases

Often, the propositions in the refinements can get rather long and
verbose. You can write predicate aliases like so:

    {-@ predicate Lt X Y = X < Y        @-}
    {-@ predicate Ge X Y = not (Lt X Y) @-}

and then use the aliases inside refinements, [for example](tests/pos/pred.hs)

    {-@ incr :: x:{v:Int | (Pos v)} -> { v:Int | ((Pos v) && (Ge v x))} @-}
    incr :: Int -> Int
    incr x = x + 1

See [Data.Map](benchmarks/esop2013-submission/Base.hs) for a more substantial
and compelling example.

**Syntax:** The key requirements for type aliases are:

- Value parameters are specified in **upper**case: `X`, `Y`, `Z` etc.


#### Failing Specifications 

The `fail b` declaration checks that the definition of `b` is unsafe. E.g., the followin is SAFE.

    {-@ fail unsafe @-}
    {-@ unsafe :: () -> { 0 == 1 } @-}
    unsafe :: () -> () 
    unsafe _ = ()

An error is created if `fail` definitions are safe or binders defined as `fail` are used by (failing or not) definitions. 


#### Type Aliases


Similarly, it is often quite tedious to keep writing

    {v: Int | v > 0}

Thus, LiquidHaskell supports refinement-type aliases of the form:

    {-@ type Gt      N = {v: Int | N <  v} @-}
    {-@ type GeNum a N = {v: a   | N <= v} @-}

or

    {-@ type SortedList a = [a]<{\fld v -> (v >= fld)}> @-}

or

    {-@ type OMap k a = Map <{\root v -> v < root}, {\root v -> v > root}> k a @-}

or

    {-@ type MinSPair a = (a, OSplay a) <\fld -> {v : Splay {v:a|v>fld} | 0=0}> @-}

and then use the above in signatures like:

    {-@ incr: x: Int -> GeNum Int x @-}

or

    {-@ incr: x: Int -> Gt x @-}

and:

    {-@ assert insert :: (Ord a) => a -> SortedList a -> SortedList a @-}

see [tests/pos/ListSort.hs](tests/pos/ListSort.hs)

and:

    {-@ assert insert :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}

see [tests/pos/Map.hs](tests/pos/Map.hs)

**Syntax:** The key requirements for type aliases are:

1. Type parameters are specified in **lower**case: `a`, `b`, `c` etc.
2. Value parameters are specified in **upper**case: `X`, `Y`, `Z` etc.


Infix  Operators
---------------------

You can define infix types and logical operators in logic [Haskell's infix notation](https://www.haskell.org/onlinereport/decls.html#fixity).
For example, if `(+++)` is defined as a measure or reflected function, you can use it infix by declaring

    {-@ infixl 9 +++ @-}


Note: infix operators cannot contain the dot character `.`.

If `(==>)` is a Haskell infix type ([see](tests/pos/T1567.hs)) 

    infixr 1 ==> 

then to use it as infix in the refinements types you need to add the refinement infix notation. 

    {-@ infixr 1 ==> @-}
    {-@ test :: g:(f ==> g) -> f x -> f y -> ()  @-} 


Specifying Measures
-------------------

Can be placed in .spec file or in .hs/.lhs file wrapped around `{-@ @-}`

Value measures: [include/GHC/Base.spec](include/GHC/Base.spec)

    measure len :: forall a. [a] -> GHC.Types.Int
    len ([])     = 0
    len (y:ys)   = 1 + len(ys)

Propositional measures: [tests/pos/LambdaEval.hs](tests/pos/LambdaEval.hs)

    {-@
    measure isValue      :: Expr -> Bool
    isValue (Const i)    = true
    isValue (Lam x e)    = true
    isValue (Var x)      = false
    isValue (App e1 e2)  = false
    isValue (Plus e1 e2) = false
    isValue (Fst e)      = false
    isValue (Snd e)      = false
    isValue (Pair e1 e2) = ((? (isValue(e1))) && (? (isValue(e2))))
    @-}

Raw measures: [tests/pos/meas8.hs](tests/pos/meas8.hs)

    {-@ measure rlen :: [a] -> Int
    rlen ([])   = {v | v = 0}
    rlen (y:ys) = {v | v = (1 + rlen(ys))}
    @-}

Generic measures: [tests/pos/Class.hs](tests/pos/Class.hs)

    {-@ class measure size :: a -> Int @-}
    {-@ instance measure size :: [a] -> Int
        size ([])   = 0
        size (x:xs) = 1 + (size xs)
    @-}
    {-@ instance measure size :: Tree a -> Int
        size (Leaf)       = 0
        size (Node x l r) = 1 + (size l) + (size r)
    @-}

**Note:** Measure names **do not** have to be the same as
field name, e.g. we could call the measure `sz` in the above
as shown in [tests/pos/Class2.hs](tests/pos/Class2.hs).


Haskell Functions as Measures (beta): [tests/pos/HaskellMeasure.hs](tests/pos/HaskellMeasure.hs)

Inductive Haskell Functions from Data Types to some type can be lifted to logic

```haskell
    {-@ measure llen @-}
    llen        :: [a] -> Int
    llen []     = 0
    llen (x:xs) = 1 + llen xs
```

The above definition
  - refines list's data constructors types with the llen information, and
  - specifies a singleton type for the haskell function
        `llen :: xs:[a] -> {v:Int | v == llen xs}`
    If the user specifies another type for llen, say
        `llen :: xs:[a] -> {v:Int | llen xs >= 0}`
    then the auto generated singleton type is overwritten.

Inlines 
-------

The `inline`  lets you use a Haskell function in a type specification. 

```
{-@ inline max @-}
{-@ max :: Int -> Int -> Int @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y
```

For example, if you write the above you can then write a function:

```haskell 
{-@ floor :: x:Int -> {v:Int | max 0 x} @-}
floor :: Int -> Int
floor x 
  | x <= 0    = 0
  | otherwise = x
``` 

That is, you can use the haskell `max` in the refinement type and 
it will automatically get “expanded” out to the full definition. 
This makes it useful e.g. to reuse plain Haskell code to compose 
specifications, and to share definitions common to refinements and code.

However, as they are *expanded* at compile time, `inline` functions 
**cannot be recursive**. The can call _other_ (non-recursive) inline functions.

If you want to talk about arbitrary (recursive) functions inside your types, 
then you need to use `reflect` described [in the blog] (https://ucsd-progsys.github.io/liquidhaskell-blog/tags/reflection.html)

Self-Invariants
===============

Sometimes, we require specifications that allow *inner* components of a
type to refer to the *outer* components, typically, to measure-based
properties of outer components. For example, the following invariant
about `Maybe` values

    {-@ type IMaybe a = {v0 : Maybe {v : a | ((isJust v0) && v = (fromJust v0))} | 0 = 0 } @-}

states that the *inner* `a` enjoys the property that the *outer* container
is definitely a `Just` and furthermore, the inner value is exactly the same
as the `fromJust` property of the outer container.

As another example, suppose we have a [measure](include/Data/Set.spec):

    measure listElts :: [a] -> (Set a)
    listElts([])   = {v | (? Set_emp(v))}
    listElts(x:xs) = {v | v = Set_cup(Set_sng(x), listElts(xs)) }

Now, all lists enjoy the property

    {-@ type IList a = {v0 : List  {v : a | (Set_mem v (listElts v0)) } | true } @-}

which simply states that each *inner* element is indeed, a member of the
set of the elements belonging to the entire list.

One often needs these *circular* or *self* invariants to connect different
levels (or rather, to *reify* the connections between the two levels.) See
[this test](tests/pos/maybe4.hs) for a simple example and `hedgeUnion` and
[Data.Map.Base](benchmarks/esop2013-submission/Base.hs) for a complex one.



Abstract and Bounded Refinements
================================

This is probably the best example of the abstract refinement syntax:

+ [Abstract Refinements](tests/pos/Map.hs)
+ [Bounded Refinements](benchmarks/icfp15/pos/Overview.lhs)

Unfortunately, the best documentation for these two advanced features
is the relevant papers at

+ [ESOP 2013](https://ranjitjhala.github.io/static/abstract_refinement_types.pdf)
+ [ICFP 2015](https://arxiv.org/abs/1507.00385)

The bounds correspond to Horn implications between abstract refinements,
which, as in the classical setting, correspond to subtyping constraints
that must be satisfied by the concrete refinements used at any call-site.

Dependent Pairs
===============
Dependent Pairs are expressed by binding the initial tuples of the pair. For example
`incrPair` defines an increasing pair.

    {-@ incrPair :: Int -> (x::Int, {v:Int | x <= v}) @-}
    incrPair i = (i, i+1)

Internally dependent pairs are implemented using abstract refinement types.
That is `(x::a, {v:b | p x})` desugars to `(a,b)<\x -> {v:b | p x}>`.

Invariants
==========

LH lets you locally associate invariants with specific data types.

For example, in [tests/measure/pos/Using00.hs](tests/measure/pos/Using00.hs) every
list is treated as a Stream. To establish this local invariant one can use the
`using` declaration

    {-@ using ([a]) as  {v:[a] | (len v > 0)} @-}

denoting that each list is not empty.

Then, LiquidHaskell will prove that this invariant holds, by proving that *all
calls* to List's constructors (ie., `:` and `[]`) satisfy it, and
will assume that each list element that is created satisfies
this invariant.

With this, at the [above](tests/measure/neg/Using00.hs) test LiquidHaskell
proves that taking the `head` of a list is safe.
But, at [tests/measure/neg/Using00.hs](tests/measure/neg/Using00.hs) the usage of
`[]` falsifies this local invariant resulting in an "Invariant Check" error.


**WARNING:** There is an older _global_ invariant mechanism that
attaches a refinement to a datatype globally.
Do not use this mechanism -- it is *unsound* and about to
deprecated in favor of something that is [actually sound](https://github.com/ucsd-progsys/liquidhaskell/issues/126)

For example,  the length of a list cannot be negative

    {-@ invariant {v:[a] | (len v >= 0)} @-}

LiquidHaskell can prove that this invariant holds, by proving that all List's
constructors (ie., `:` and `[]`) satisfy it.(TODO!) Then, LiquidHaskell
assumes that each list element that is created satisfies
this invariant.


Rewriting
=========

*Experimental*

You use the `rewriteWith` annotation to indicate equalities that PLE will apply automatically. For example, suppose that you have proven associativity
of `++` for lists.

``` haskell
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
```

Using the `rewriteWith` annotation, PLE will automatically apply the equality for associativity whenever it encounters an expression of the form `xs ++ (ys ++ zs)` or `(xs ++ ys) ++ zs`. For example, you can prove `assoc2` for free.

``` haskell
{-@ rewriteWith assoc2 [assoc] @-} 
{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws } @-}
assoc2 :: [a] -> [a] -> [a] -> [a] -> ()
assoc2 xs ys zs ws = () 
```

You can also annotate a function as being a global rewrite rule by using the
`rewrite` annotation, in which case PLE will apply it across the entire module.

``` haskell
{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
```


### Limitations

Currently, rewriting does not work if the equality that uses the rewrite rule
includes parameters that contain inner refinements ([test](tests/errors/ReWrite5.hs)).

Rewriting works by pattern-matching expressions to determine if there is a
variable substitution that would allow it to match against either side of a
rewrite rule. If so, that substitution is applied to the opposite side and the
corresponding equality is generated. If one side of the equality contains any
parameters that are not bound on the other side, it will not be possible to
generate a rewrite in that direction, because those variables cannot be
instantiated. Likewise, if there are free variables on both sides of an
equality, no rewrite can be generated at all ([test](tests/errors/ReWrite7.hs)).

It's possible in theory for rewriting rules to diverge. We have a simple check 
to ensure that rewriting rules that will always diverge do not get instantiated. 
However, it's possible that applying a combination of rewrite rules could cause
divergence.

Formal Grammar of Refinement Predicates
=======================================

(C)onstants
-----------

    c := 0, 1, 2, ...

(V)ariables
-----------

    v := x, y, z, ...


(E)xpressions
-------------

    e := v                      -- variable
       | c                      -- constant
       | (e + e)                -- addition
       | (e - e)                -- subtraction
       | (c * e)                -- multiplication by constant
       | (v e1 e2 ... en)       -- uninterpreted function application
       | (if p then e else e)   -- if-then-else

(R)elations
-----------

    r := ==               -- equality
       | /=               -- disequality
       | >=               -- greater than or equal
       | <=               -- less than or equal
       | >                -- greater than
       | <                -- less than


(P)redicates
------------

    p := (e r e)          -- binary relation
       | (v e1 e2 ... en) -- predicate (or alias) application
       | (p && p)         -- and
       | (p || p)         -- or
       | (p => p)         -- implies
       | (not p)          -- negation
       | true
       | false


Specifying Qualifiers
=====================

There are several ways to specify qualifiers.

By Separate `.hquals` Files
---------------------------

You can write qualifier files e.g. [Prelude.hquals](include/Prelude.hquals)

If a module is called or imports

    Foo.Bar.Baz

Then the system automatically searches for

    include/Foo/Bar/Baz.hquals

By Including `.hquals` Files
----------------------------

Additional qualifiers may be used by adding lines of the form:

    {-@ include <path/to/file.hquals> @-}

to the Haskell source. See, [this](tests/pos/meas5.hs) for example.


In Haskell Source or Spec Files
-------------------------------

Finally, you can specifiers directly inside source (.hs or .lhs) or spec (.spec)
files by writing as shown [here](tests/pos/qualTest.hs)

    {-@ qualif Foo(v:Int, a: Int) : (v = a + 100)   @-}


**Note** In addition to these, LiquidHaskell scrapes qualifiers from all
the specifications you write i.e.

1. all imported type signatures,
2. measure bodies and,
3. data constructor definitions.



## Termination Metrics

In recursive functions the *first* algebraic or integer argument should be decreasing.

The default decreasing measure for lists is length and Integers its value.

### Default Termination Metrics

The user can specify the *size* of a data-type in the data definition

```haskell
    {-@ data L [llen] a = Nil | Cons { x::a, xs:: L a} @-}
```

In the above, the measure `llen`, which needs to be defined by the user
(see below), is defined as the *default metric* for the type `L a`. LH
will use this default metric to _automatically_ prove that the following
terminates:

```haskell
    append :: L a -> L a -> L a  
    append N           ys = ys
    append (Cons x xs) ys = Cons x (append xs ys)
```

as, by default the *first* (non-function) argument with an
associated size metric is checked to be strictly terminating
and non-negative at each recursive call.

A default termination metric is a Haskell function that is proved terminating 
using structural induction. To deactivate structional induction check on the 
termination metric, use the `--trust-sizes` flag. 
### Explicit Termination Metrics

However, consider the function `reverse`

```haskell
    reverseAcc :: L a -> L a -> L a  
    reverseAcc acc N           = acc
    reverseAcc acc (Cons x xs) = reverseAcc (Cons x acc) xs
```

Here, the first argument does not decrease, instead
the second does. We can tell LH to use the second
argument using the *explicit termination metric*

```haskell
    reverseAcc :: L a -> xs:L a -> L a / [llen xs]  
```  

which tells LH that the `llen` of the second argument `xs`
is what decreases at each recursive call.

Decreasing expressions can be arbitrary refinement expressions, e.g.,

```haskell
    {-@ merge :: Ord a => xs:L a -> ys:L a -> L a / [llen xs + llen ys] @-}
```

states that at each recursive call of `merge` the _sum of the lengths_
of its arguments will decrease.

### Lexicographic Termination Metrics

Some functions do not decrease on a single argument, but rather a
combination of arguments, e.g. the Ackermann function.

```haskell
    {-@ ack :: m:Int -> n:Int -> Nat / [m, n] @-}
    ack m n
      | m == 0          = n + 1
      | m > 0 && n == 0 = ack (m-1) 1
      | m > 0 && n >  0 = ack (m-1) (ack m (n-1))
```

In all but one recursive call `m` decreases, in the final call `m`
does not decrease but `n` does. We can capture this notion of `m`
normally decreases, but if it does not, `n` will decrease with a
*lexicographic* termination metric `[m, n]`.


An alternative way to express this specification is by annotating
the function's type with the appropriate *numeric* decreasing expressions.
As an example, you can give `ack` a type

    {-@ ack :: m:Nat -> n:Nat -> Nat / [m,n] @-}

stating that the *numeric* expressions `[m, n]` are lexicographically decreasing.

### Mutually Recursive Functions

When dealing with mutually recursive functions you may run into a
situation where the decreasing parameter must be measured *across* a
series of invocations, e.g.

```haskell
    even :: Int -> Bool
    even 0 = True
    even n = odd (n-1)

    odd :: Int -> Bool
    odd  n = not (even n)
```

In this case, you can introduce a ghost parameter that *orders the functions*

```haskell
    {-@ isEven :: n:Nat -> Bool / [n, 0] @-}
    isEven :: Int -> Bool
    isEven 0 = True
    isEven n = isOdd (n-1)

    {-@ isOdd :: n:Nat -> Bool / [n, 1] @-}
    isOdd :: Int -> Bool
    isOdd  n = not $ isEven n
```

thus recovering a decreasing measure for the pair of functions, the
pair of arguments. This can be encoded with the lexicographic
termination annotation as shown above.
See [tests/pos/mutrec.hs](tests/pos/mutrec.hs) for the full example.

### Automatic Termination Metrics

Apart from specifying a specific decreasing measure for
an Algebraic Data Type, the user can specify that the ADT
follows the expected decreasing measure by

```haskell
    {-@ autosize L @-}
```

Then, LH will define an instance of the function `autosize`
for `L` that decreases by 1 at each recursive call and use
`autosize` at functions that recurse on `L`.

For example, `autosize L` will refine the data constructors
of `L a` with the `autosize :: a -> Int` information, such
that

```haskell
    Nil  :: {v:L a | autosize v = 0}
    Cons :: x:a -> xs:L a -> {v:L a | autosize v = 1 + autosize xs}
```

Also, an invariant that `autosize` is non negative will be generated

```haskell
    invariant  {v:L a| autosize v >= 0 }
```

This information is all LiquidHaskell needs to prove termination
on functions that recurse on `L a` (on ADTs in general.)

### Disabling Termination Checking

To *disable* termination checking for `foo` that is,
to *assume* that it is terminating (possibly for some
complicated reason currently beyond the scope of LH)
you can write

```haskell
    {-@ lazy foo @-}
```

## Synthesis

LH has some very preliminary support for program synthesis.

### How to use it

Activate the flag for typed holes in LiquidHaskell. E.g.
from command line: 
    
    liquid --typedholes

In a Haskell source file: 
    
    {-@ LIQUID --typed-holes @-}

Using the flag for typed holes, two more flags can be used:

- **max-match-depth**: Maximum number of pattern match expressions used during synthesis (default value: 4).

- **max-app-depth**: Maximum number of same function applications used during synthesis (default value: 2).

Having the program specified in a Haskell source file, use 
GHC' s hole variables, e.g.:

    {-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
    myMap :: (a -> b) -> [a] -> [b]
    myMap = _goal

### Limitations

This is an experimental feature, so potential users could only 
expect to synthesize programs, like [these](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/tests/synth).

Current limitations include:

- No boolean conditionals are synthesized.
- Holes can only appear at top level, e.g.: 

        {-@ f :: x: [a] -> { v: [a] | v == x } @-}
        f :: [a] -> [a]
        -- This works
        f = _hole
        -- This does not work
        f x = _hole

- Only one hole can appear in each module.