![LiquidHaskell](/resources/logo.png)


[![Hackage](https://img.shields.io/hackage/v/liquidhaskell.svg)](https://hackage.haskell.org/package/liquidhaskell) [![Hackage-Deps](https://img.shields.io/hackage-deps/v/liquidhaskell.svg)](http://packdeps.haskellers.com/feed?needle=liquidhaskell) [![Build Status](https://img.shields.io/circleci/project/ucsd-progsys/liquidhaskell/master.svg)](https://circleci.com/gh/ucsd-progsys/liquidhaskell)


Requirements
------------

LiquidHaskell requires (in addition to the cabal dependencies)

- SMTLIB2 compatible solver

How To Clone, Build and Install
-------------------------------

See [install instructions](INSTALL.md)

How To Run
----------

To verify a file called `foo.hs` at type

    $ liquid foo.hs

How to Run inside GHCi
----------------------

To run inside `ghci` e.g. when developing do:

    $ stack ghci liquidhaskell
    ghci> :m +Language.Haskell.Liquid.Liquid
    ghci> liquid ["tests/pos/Abs.hs"]

How To Run Regression Tests
---------------------------

    $ make test

To use threads to speed up the tests

    $ make THREADS=30 test

Or your favorite number of threads, depending on cores etc.

You can directly extend and run the tests by modifying

    tests/test.hs

To run the regression test *and* the benchmarks run

    $ make all-test

How to Profile
--------------

1. Build with profiling on

    ```
    $ make pdeps && make prof
    ```

2. Run with profiling

    ```
    $ time liquid range.hs +RTS -hc -p
    $ time liquid range.hs +RTS -hy -p
    ```

    Followed by this which shows the stats file

    ```
    $ more liquid.prof
    ```

    or by this to see the graph

    ```
    $ hp2ps -e8in -c liquid.hp
    $ gv liquid.ps
    ```

    etc.

How to Get Stack Traces On Exceptions
-------------------------------------

1. Build with profiling on

    ```
    $ make pdeps && make prof
    ```

2. Run with backtraces

    ```
    $ liquid +RTS -xc -RTS foo.hs
    ```

Working With Submodules
-----------------------

 - To update the `liquid-fixpoint` submodule, run

    ```
    cd ./liquid-fixpoint
    git fetch --all
    git checkout <remote>/<branch>
    cd ..
    ```

   This will update `liquid-fixpoint` to the latest version on `<branch>`
   (usually `master`) from `<remote>` (usually `origin`).

 - After updating `liquid-fixpoint`, make sure to include this change in a
   commit! Running

    ```
    git add ./liquid-fixpoint
    ```

   will save the current commit hash of `liquid-fixpoint` in your next commit
   to the `liquidhaskell` repository.

 - For the best experience, **don't** make changes directly to the
   `./liquid-fixpoint` submodule, or else git may get confused. Do any
   `liquid-fixpoint` development inside a separate clone/copy elsewhere.

 - If something goes wrong, run

    ```
    rm -r ./liquid-fixpoint
    git submodule update --init
    ```

   to blow away your copy of the `liquid-fixpoint` submodule and revert to the
   last saved commit hash.

 - Want to work fully offline? git lets you add a local directory as a remote.
   Run

    ```
    cd ./liquid-fixpoint
    git remote add local /path/to/your/fixpoint/clone
    cd ..
    ```

   Then to update the submodule from your local clone, you can run

    ```
    cd ./liquid-fixpoint
    git fetch local
    git checkout local/<branch>
    cd ..
    ```

 - Updating `prover` submodule follows similarly

Command Line Options
====================

LiquidHaskell supports several command line options, to configure the
checking. Each option can be passed in at the command line, or directly
added to the source file via:

    {-@ LIQUID "option-within-quotes" @-}

for example, to disable termination checking (see below)

    {-@ LIQUID "--notermination" @-}

You may also put command line options in the environment variable
`LIQUIDHASKELL_OPTS`. For example, if you add the line:

    LIQUIDHASKELL_OPTS="--diff"

to your `.bashrc` then, by default, all files will be
*incrementally checked* unless you run with the overriding
`--full` flag (see below).

Incremental Checking
--------------------

LiquidHaskell supports *incremental* checking where each run only checks
the part of the program that has been modified since the previous run.

    $ liquid --diff foo.hs

Each run of `liquid` saves the file to a `.bak` file and the *subsequent*
run
    + does a `diff` to see what has changed w.r.t. the `.bak` file
    + only generates constraints for the `[CoreBind]` corresponding to the
       changed top-level binders and their transitive dependencies.

The time savings are quite significant. For example:

    $ time liquid --notermination -i . Data/ByteString.hs > log 2>&1

    real	7m3.179s
    user	4m18.628s
    sys	    0m21.549s

Now if you go and tweak the definition of `spanEnd` on line 1192 and re-run:

    $ time liquid -d --notermination -i . Data/ByteString.hs > log 2>&1

    real	0m11.584s
    user	0m6.008s
    sys	    0m0.696s

The diff is only performed against **code**, i.e. if you only change
specifications, qualifiers, measures, etc. `liquid -d` will not perform
any checks. In this case, you may specify individual definitions to verify:

    $ liquid -b bar -b baz foo.hs

This will verify `bar` and `baz`, as well as any functions they use.

If you always want to run a given file with diff-checking, add
the pragma:

    {-@ LIQUID "--diff" @-}


Full Checking (DEFAULT)
-----------------------

To force LiquidHaskell to check the **whole** file (DEFAULT), use:

    $ liquid --full foo.hs

to the file. This will override any other `--diff` incantation
elsewhere (e.g. inside the file.)


If you always want to run a given file with full-checking, add
the pragma:

    {-@ LIQUID "--full" @-}

Specifying Different SMT Solvers
--------------------------------

By default, LiquidHaskell uses the SMTLIB2 interface for Z3.

To run a different solver (supporting SMTLIB2) do:

    $ liquid --smtsolver=NAME foo.hs

Currently, LiquidHaskell supports

+ [CVC4](http://cvc4.cs.nyu.edu/)
+ [MathSat](http://mathsat.fbk.eu/download.html )

To use these solvers, you must install the corresponding binaries
from the above web-pages into your `PATH`.

You can also build and link against the Z3 API (faster but requires more
dependencies). If you do so, you can use that interface with:

    $ liquid --smtsolver=z3mem foo.hs


Short Error Messages
--------------------

By default, subtyping error messages will contain the inferred type, the
expected type -- which is **not** a super-type, hence the error -- and a
context containing relevant variables and their type to help you understand
the error. If you don't want the above and instead, want only the
**source position** of the error use:

    --short-errors

Short (Unqualified) Module Names
-------------------------------

By default, the inferred types will have fully qualified module names.
To use unqualified names, much easier to read, use:

    --short-names


Totality Check
--------------

LiquidHaskell can prove the absence of pattern match failures.
Use the `totality` flag to prove that all defined functions are total.

    liquid --totality test.hs

For example, the definition

    fromJust :: Maybe a -> a
    fromJust (Just a) = a

is not total and it will create an error message.
If we exclude `Nothing` from its domain, for example using the following specification

    {-@ fromJust :: {v:Maybe a | (isJust v)} -> a @-}

`fromJust` will be safe.

Termination Check
-----------------

By **default** a termination check is performed on all recursive functions.

Use the `no-termination` option to disable the check

    liquid --no-termination test.hs

In recursive functions the *first* algebraic or integer argument should be decreasing.

The default decreasing measure for lists is length and Integers its value.

The user can specify the decreasing measure in data definitions:

    {-@ data L [llen] a = Nil | Cons (x::a) (xs:: L a) @-}

Defines that `llen` is the decreasing measure (to be defined by the user).

For example, in the function `foldl`

    foldl k acc N           = acc
    foldl k acc (Cons x xs) = foldl k (x `k` acc) xs

by default the *second* argument (the first non-function argument) will be
checked to be decreasing. However, the explicit hint

    {-@ Decrease foo 3 @-}

tells LiquidHaskell to instead use the *third* argument.

Apart from specifying a specific decreasing measure for an Algebraic Data Type,
the user can specify that the ADT follows the expected decreasing measure by

    {-@ autosize L @-}

Then, LiquidHaskell will define an instance of the function `autosize` for `L` that decreases by 1 at each recursive call and use `autosize` at functions that recurse on `L`.

For example, `autosize L` will refine the data constroctors of `L a` with the `autosize :: a -> Int` information, such that

    Nil  :: {v:L a | autosize v = 0}
    Cons :: x:a -> xs:L a -> {v:L a | autosize v = 1 + autosize xs}

Also, an invariant that `autosize` is non negative will be generated

    invariant  {v:L a| autosize v >= 0 }

This information is all LiquidHaskell needs to prove termination on functions that recurse on `L a` (on ADTs in general.)


To *disable* termination checking for `foo` that is, to *assume* that it
is terminating (possibly for some complicated reason currently beyond the
scope of LiquidHaskell) you can write

    {-@ Lazy foo @-}

Some functions do not decrease on a single argument, but rather a
combination of arguments, e.g. the Ackermann function.

    ack m n
      | m == 0          = n + 1
      | m > 0 && n == 0 = ack (m-1) 1
      | m > 0 && n >  0 = ack (m-1) (ack m (n-1))

In all but one recursive call `m` decreases, in the final call `m`
does not decrease but `n` does. We can capture this notion of "x
normally decreases, but if it does not, y will" with an extended
annotation

    {-@ Decrease ack 1 2 @-}

An alternative way to express this specification is by annotating
the function's type with the appropriate *numeric* decreasing expressions.
As an example, you can give `ack` a type

    {-@ ack :: m:Nat -> n:Nat -> Nat / [m,n] @-}

stating that the *numeric* expressions `[m, n]` are lexicographically decreasing.

Decreasing expressions can be arbitrary refinement expressions, e.g.,

    {-@ merge :: Ord a => xs:[a] -> ys:[a] -> [a] / [(len xs) + (len ys)] @-}

states that at each recursive call of `merge` the sum of the lengths
of its arguments will be decreased.

When dealing with mutually recursive functions you may run into a
situation where the decreasing parameter must be measured *across* a
series of invocations, e.g.

    even 0 = True
    even n = odd (n-1)

    odd  n = not $ even n

In this case, you can introduce a ghost parameter that orders the *functions*

    even 0 _ = True
    even n _ = odd (n-1) 1

    odd  n _ = not $ even n 0

thus recovering a decreasing measure for the pair of functions, the
pair of arguments. This can be encoded with the lexicographic
termination annotation `{-@ Decrease even 1 2 @-}` (see
[tests/pos/mutrec.hs](tests/pos/mutrec.hs) for the full example).

Lazy Variables
--------------

A variable can be specified as `LAZYVAR`

    {-@ LAZYVAR z @-}

With this annotation the definition of `z` will be checked at the points where
it is used. For example, with the above annotation the following code is SAFE:

    foo   = if x > 0 then z else x
      where
        z = 42 `safeDiv` x
        x = choose 0

By default, all the variables starting with `fail` are marked as LAZY, to defer
failing checks at the point where these variables are used.

Prune Unsorted Predicates
-------------------------

By default unsorted predicates are pruned away (yielding `true`
for the corresponding refinement.) To disable this behaviour
use the `no-prune-unsorted` flag.

    liquid --no-prune-unsorted test.hs


Case Expansion
-------------------------

By default LiquidHaskell expands all data constructors to the case statements.
For example,
if `F = A1 | A2 | .. | A10`,
then liquidHAskell will expand the code
`case f of {A1 -> True; _ -> False}`
to `case f of {A1 -> True; A2 -> False; ...; A10 -> False}`.
This expansion can lead to more precise code analysis
but it can get really expensive due to code explosion.
The `no-case-expand` flag prevents this expansion and keeps the user
provided cases for the case expression.

    liquid --no-case-expand test.hs


Higher order logic
-------------------
The flag `--higherorder` allows reasoning about higher order functions.


Restriction to Linear Arithmetic
---------------------------------
When using `z3` as the solver, LiquidHaskell allows for non-linear arithmetic:
division and multiplication on integers are interpreted by `z3`. To treat division
and multiplication as unintepreted functions use the `linear` flag

    liquid --linear test.hs

Counter examples (Experimental!)
--------------------------------
When given the `--counter-examples` flag, LiquidHaskell will attempt to produce
counter-examples for the type errors it discovers. For example, see
[tests/neg/ListElem.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/neg/ListElem.hs)

```
% liquid --counter-examples tests/neg/ListElem.hs

...

tests/neg/ListElem.hs:12:1-8: Error: Liquid Type Mismatch

 12 | listElem _ []      = False
      ^^^^^^^^

   Inferred type
     VV : {VV : Bool | VV == True}
     VV = True

   not a subtype of Required type
     VV : {VV : Bool | Prop VV <=> Set_mem ?b (listElts ?a)}

   In Context
     ?a : {?a : [a] | len ?a >= 0}
     ?a = [1]

     ?b : a
     ?b = 0
```

The `--counter-examples` flag requires that each type in the context be
an instance of `GHC.Generics.Generic` or `Test.Targetable.Targetable`
(provided as part of LiquidHaskell).  LiquidHaskell cannot generate
counter-examples for polymorphic types, but will try (naively) to
instantiate type variables with `Int` (as seen in the example above).

Writing Specifications
======================

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
    data Map k a <l :: k -> k -> Bool, r :: k -> k -> Bool>
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
[For example](tests/pos/LiquidClass.hs)

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

    {-@ measure llen @-}
    llen        :: [a] -> Int
    llen []     = 0
    llen (x:xs) = 1 + llen xs

The above definition
  - refines list's data constructors types with the llen information, and
  - specifies a singleton type for the haskell function
        `llen :: xs:[a] -> {v:Int | v == llen xs}`
    If the user specifies another type for llen, say
        `llen :: xs:[a] -> {v:Int | llen xs >= 0}`
    then the auto generated singleton type is overwriten.

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

As another example, suppose we have a [measure](include/Data/Set/Set.spec):

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

Bounds
======
The bounds correspond to Horn
implications between abstract refinements, which, as in the classical
setting, correspond to subtyping constraints that must be satisfied by the concrete refinements used at any call-site.

See `benchmarks/icfp15/pos/Overview.lhs` for exaples on how to use bounds.


Invariants
==========

**WARNING:** Do not use this mechanism -- it is *unsound* and about to be
replaced with something that is [actually sound](https://github.com/ucsd-progsys/liquidhaskell/issues/126)

There are two ways of specifying invariants in LiquidHaskell.
First, there are *global* invariants that always hold for a data-type. For
example,  the length of a list cannot be negative

    {-@ invariant {v:[a] | (len v >= 0)} @-}

LiquidHaskell can prove that this invariant holds, by proving that all List's
constractos (ie., `:` and `[]`) satisfy it.(TODO!)
Then, LiquidHaskell assumes that each list element that is created satisfies
this invariant.

Second, there are *local* invariants that one may use. For
example, in [tests/pos/StreamInvariants.hs](tests/pos/StreamInvariants.hs) every
list is treated as a Stream. To establish this local invariant one can use the
`using` declaration

    {-@ using ([a]) as  {v:[a] | (len v > 0)} @-}

denoting that each list is not empty.
Then, LiquidHaskell will prove that this invariant holds, by proving that *all
calls* to List's constructors (ie., `:` and `[]`) satisfy it, and
will assume that each list element that is created satisfies
this invariant.

With this, at the [above](tests/neg/StreamInvariants.hs) test LiquidHaskell
proves that taking the `head` of a list is safe.
But, at [tests/neg/StreamInvariants.hs](tests/neg/StreamInvariants.hs) the usage of
`[]` falsifies this local invariant resulting in an "Invariant Check" error.

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
       | (c * e)                -- cmultiplication by constant
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


Generating HTML Output
======================

The system produces HTML files with colorized source, and mouseover
inferred type annotations, which are quite handy for debugging failed
verification attempts.

- **Regular Haskell** When you run: `liquid foo.hs` you get a file
  `foo.hs.html` with the annotations. The coloring is done using
  `hscolour`.

- **Markdown + Literate Haskell** You can also feed in literate haskell files
  where the comments are in [Pandoc markdown](http://johnmacfarlane.net/pandoc/demo/example9/pandocs-markdown.html).
  In this case, the tool will run `pandoc` to generate the HTML from the comments.
  Of course, this requires that you have `pandoc` installed as a binary on
  your system. If not, `hscolour` is used to render the HTML.

  It is also possible to generate *slide shows* from the above.
  See the [tutorial directory](docs/tutorial) for an example.

Editor Integration
==================

+ [Emacs/Flycheck](https://github.com/ucsd-progsys/liquid-types.el)
+ [Vim/Syntastic](https://github.com/ucsd-progsys/liquid-types.vim)

Command Line Options
====================

To see all options, run `liquid --help`. Here are some common options:

- `--cabaldir` will automatically find a .cabal file in the ancestor
  path from which the target file belongs, and then add the relevant
  source and dependencies to the paths searched for by LiquidHaskell.

  This means we don't have to manually do `-i src` etc. when checking
  large projects, which can be tedious e.g. within emacs.

- `--diff` performs differential checking, i.e. only checks those binders
  that have transitively affected by edits since the previous check.
  Can speed things up greatly during editing.

- `--short-names` prints out non-qualified names i.e. `Int` instead of
  `GHC.Types.Int` for inferred type annotations and error messages.

**Pragmas** are useful for embedding options directly within the source file,
that is, somewhere in the file (perhaps at the top) put in:

    {-@ LIQUID "--diff"        @-}
    {-@ LIQUID "--short-names" @-}
    {-@ LIQUID "--cabaldir"    @-}

to have the relevant option be used for that file.

Generating Performance Reports
------------------------------

We have set up infrastructure to generate performance reports using [Gipeda](https://github.com/nomeata/gipeda).

Gipeda will generate a static webpage that tracks the peformance improvements
and regressions between commits. To generate the site, first ensure you have the
following dependencies available:

* Git
* Cabal >= 1.18
* GHC
* Make
* Bash (installed at `/bin/bash`)

After ensuring all dependencies are available, from the Liquid Haskell
directory, execute:

    cd scripts/performance
    ./deploy-gipeda.bash

This will download and install all the relevant repositories and files. Next, to
generate the performance report, use the `generate-site.bash` script. This script
has a few options:

* `-s [hash]`: Do not attempt to generate performance reports for any commit
older than the commit specified by the entered git hash
* `-e [hash]`: Do not attempt to generate performance reports for any commit
newer than the commit specified by the entered git hash
* `-f`: The default behavior of `generate-site.bash` is to first check if logs
have been created for a given hash. If logs already exist, `generate-site.bash`
will not recreate them. Specify this option to skip this check and regenerate
all logs.

You should expect this process to take a very long time. `generate-site.bash`
will compile each commit, then run the entire test suite and benchmark suite
for each commit. It is suggested to provide a managable range to `generate-site.bash`:

    ./generate-site.bash -s [starting hash] -e [ending hash]

...will generate reports for all commits between (inclusive) [starting hash]
and [ending hash].

    ./generate-site.bash -s [starting hash]

... will generate reports for all commits newer than [starting hash]. This command
can be the basis for some automated report generation process (i.e. a cron job).

Finally, to remove the Gipeda infrastructure from your computer, you may execute:

    ./cleanup-gipeda.bash

...which will remove any files created by `deploy-gipeda.bash` and `generate-site.bash`
from your computer.

Configuration Management
------------------------

It is very important that the version of Liquid Haskell be maintained properly.

Suppose that the current version of Liquid Haskell is `A.B.C.D`:

+ After a release to hackage is made, if any of the components `B`, `C`, or `D` are missing, they shall be added and set to `0`. Then the `D` component of Liquid Haskell shall be incremented by `1`. The version of Liquid Haskell is now `A.B.C.(D + 1)`

+ The first time a new function or type is exported from Liquid Haskell, if any of the components `B`, or `C` are missing, they shall be added and set to `0`. Then the `C` component shall be incremented by `1`, and the `D` component shall stripped. The version of Liquid Haskell is now `A.B.(C + 1)`

+ The first time the signature of an exported function or type is changed, or an exported function or type is removed (this includes functions or types that Liquid Haskell re-exports from its own dependencies), if the `B` component is missing, it shall be added and set to `0`. Then the `B` component shall be incremented by `1`, and the `C` and `D` components shall be stripped. The version of Liquid Haskell is now `A.(B + 1)`

+ The `A` component shall be updated at the sole discretion of the project owners.
