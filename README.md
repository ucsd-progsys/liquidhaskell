![LiquidHaskell](/resources/logo.png)



[![Hackage](https://img.shields.io/hackage/v/liquidhaskell.svg)](https://hackage.haskell.org/package/liquidhaskell) [![Hackage-Deps](https://img.shields.io/hackage-deps/v/liquidhaskell.svg)](http://packdeps.haskellers.com/feed?needle=liquidhaskell) [![Build Status](https://img.shields.io/circleci/project/ucsd-progsys/liquidhaskell/master.svg)](https://circleci.com/gh/ucsd-progsys/liquidhaskell)
[![Windows build status](https://ci.appveyor.com/api/projects/status/78y7uusjcgor5p16/branch/develop?svg=true)](https://ci.appveyor.com/project/varosi/liquidhaskell-nlhra/branch/develop)

Main Web site
-------------

* [Try LiquidHaskell in your browser](http://goto.ucsd.edu:8090/index.html)
* [Splash page with examples and link to blog](https://ucsd-progsys.github.io/liquidhaskell-blog/)
* [120 minute workshop with more examples](http://ucsd-progsys.github.io/lh-workshop/01-index.html)
* [Long ish Tutorial](http://ucsd-progsys.github.io/liquidhaskell-tutorial/)

Questions
-----------
If you have any questions

* Join the Liquid Haskell [slack channel](https://join.slack.com/t/liquidhaskell/shared_invite/enQtMjY4MTk3NDkwODE3LTFmZGFkNGEzYWRkNDJmZDQ0ZGU1MzBiZWZiZDhhNmY3YTJiMjUzYTRlNjMyZDk1NDU3ZGIxYzhlOTIzN2UxNWE)
* Mail the [users mailing list](https://groups.google.com/forum/#!forum/liquidhaskell)
* Create a github issue

Contributing Guide
------------------

Please see the [contributing guide](CONTRIBUTING.md)

Requirements
------------

LiquidHaskell requires (in addition to the cabal dependencies)

- SMTLIB2 compatible solver installed and its executable found on PATH

How To Clone, Build and Install
-------------------------------

You may want to [try LiquidHaskell online](http://goto.ucsd.edu:8090/index.html)

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

See [this file](NIX.md) for instructions on running inside a custom `nix`-shell.


How To Get Editor Support
-------------------------

To get Liquid Haskell in your editor use the Haskell IDE Engine and activate the liquid plugin. 
For example, 

- [VS Code](https://code.visualstudio.com/)

    1. Install the [haskell-ide-engine](https://github.com/haskell/haskell-ide-engine)
    2. Enable Haskell Language Server extension from VS Code. 
    3. In the VS Code settings search for `liquid` and enable the `Liquid On` extension.



How To Run Regression Tests
---------------------------

You can run all the tests by

    $ stack test

To pass in specific parameters and run a subset of the tests 

    $ stack test liquidhaskell --fast  --test-arguments "--liquid-opts --no-termination -p Unit"

Or your favorite number of threads, depending on cores etc.

You can directly extend and run the tests by modifying

    tests/test.hs

How to Profile
--------------

1. Build with profiling on

    ```
    $ stack build liquidhaskell --fast --profile
    ```


2. Run with profiling

    ```
    $ stack exec -- liquid range.hs +RTS -hc -p
    $ stack exec -- liquid range.hs +RTS -hy -p
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
    $ stack build liquidhaskell --fast --profile
    ```

2. Run with backtraces

    ```
    $ liquid +RTS -xc -RTS foo.hs
    ```

    ```
    stack exec -- liquid List00.hs +RTS -p -xc -RTS
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

Command Line Options
====================

LiquidHaskell supports several command line options, to configure the
checking. Each option can be passed in at the command line, or directly
added to the source file via:

```haskell
    {-@ LIQUID "option-within-quotes" @-}
```

for example, to disable termination checking (see below)

```haskell
    {-@ LIQUID "--no-termination" @-}
```

You may also put command line options in the environment variable
`LIQUIDHASKELL_OPTS`. For example, if you add the line:

```
    LIQUIDHASKELL_OPTS="--diff"
```

to your `.bashrc` then, by default, all files will be
*incrementally checked* unless you run with the overriding
`--full` flag (see below).

Theorem Proving 
---------------

To enable theorem proving, e.g. as [described here](https://ucsd-progsys.github.io/liquidhaskell-blog/tags/reflection.html)
use the option 

```haskell
    {-@ LIQUID "--reflection" @-}
```

To additionally turn on _proof by logical evaluation_ use the option

```haskell
    {-@ LIQUID "--ple" @-}
```

You can see many examples of proofs by logical evaluation in `benchmarks/popl18/ple/pos`

This flag is **global** and will symbolically evaluate all the terms that appear in the specifications.

As an alternative, the `liquidinstanceslocal` flag has local behavior. [See](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/benchmarks/proofautomation/pos/Unification.hs)

```
{-@ LIQUID "--ple-local" @-}
```

will only evaluate terms appearing in the specifications
of the function `theorem`, in the function `theorem` is
annotated for automatic instantiation using the following
liquid annotation

```
{-@ automatic-instances theorem @-}
```

To allow reasoning about function extensionality use the `extensionality flag`. [See](https://github.com/ucsd-progsys/liquidhaskell/blob/880c78f94520d76fa13880eac050f21dacb592fd/tests/pos/T1577.hs)

```
{-@ LIQUID "--extensionality" @-}
```

Incremental Checking
--------------------

LiquidHaskell supports *incremental* checking where each run only checks
the part of the program that has been modified since the previous run.

```
    $ liquid --diff foo.hs
```

Each run of `liquid` saves the file to a `.bak` file and the *subsequent* run

    + does a `diff` to see what has changed w.r.t. the `.bak` file
    + only generates constraints for the `[CoreBind]` corresponding to the
       changed top-level binders and their transitive dependencies.

The time savings are quite significant. For example:

```
    $ time liquid --notermination -i . Data/ByteString.hs > log 2>&1

    real	7m3.179s
    user	4m18.628s
    sys	    0m21.549s
```

Now if you go and tweak the definition of `spanEnd` on line 1192 and re-run:

```
    $ time liquid -d --notermination -i . Data/ByteString.hs > log 2>&1

    real	0m11.584s
    user	0m6.008s
    sys	    0m0.696s
```

The diff is only performed against **code**, i.e. if you only change
specifications, qualifiers, measures, etc. `liquid -d` will not perform
any checks. In this case, you may specify individual definitions to verify:

```
    $ liquid -b bar -b baz foo.hs
```

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

+ [CVC4](http://cvc4.cs.stanford.edu/web/)
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

Disabling Checks on Functions
-----------------------------

You can _disable_ checking of a particular function (e.g. because it is unsafe,
or somehow not currently outside the scope of LH) by using the `ignore` directive.

For example,

```haskell
{-@ ignore foo @-}
```

will _disable_ the checking of the code for the top-level binder `foo`.

See `tests/pos/Ignores.hs` for an example.


Totality Check
--------------

LiquidHaskell proves the absence of pattern match failures.

For example, the definition

    fromJust :: Maybe a -> a
    fromJust (Just a) = a

is not total and it will create an error message.
If we exclude `Nothing` from its domain, for example using the following specification

    {-@ fromJust :: {v:Maybe a | (isJust v)} -> a @-}

`fromJust` will be safe.

Use the `no-totality` flag to disable totality checking.

    liquid --no-totality test.hs

Termination Check
-----------------

By **default** a termination check is performed on all recursive functions.

Use the `--no-termination` option to disable the check

    liquid --no-termination test.hs

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
    {-@ isEven :: n:Nat -> z:{v:Int | v = 0} -> Bool / [n, z] @-}
    isEven :: Int -> Int -> Bool
    isEven 0 _ = True
    isEven n _ = isOdd (n-1) 1

    {-@ isOdd :: n:Nat -> z:{v:Int | v = 1} -> Bool / [n, z] @-}
    isOdd :: Int -> Int -> Bool
    isOdd  n _ = not (isEven n 0)
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

Total Haskell
--------------

LiquidHaskell provides a total Haskell flag that checks both totallity and termination of the program,
overriding a potential no-termination flag.

    liquid --total-Haskell test.hs


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

No measure fields
------------------

When a data type is refined, Liquid Haskell automatically turns the data constructor fields into measures.
For example,

    {-@ data L a = N | C {hd :: a, tl :: L a} @-}

will automatically create two measures `hd` and `td`.
To deactivate this automatic measure definition, and speed up verification, you can use the `no-measure-fields` flag.

    liquid --no-measure-fields test.hs



Prune Unsorted Predicates
--------------------------

The `--prune-unsorted` flag is needed when using *measures over specialized instances* of ADTs. 

For example, consider a measure over lists of integers

```haskell
    sum :: [Int] -> Int
    sum [] = 0
    sum (x:xs) = 1 + sum xs
```

This measure will translate into strengthening the types of list constructors

```
    [] :: {v:[Int] | sum v = 0 }
    (:) :: x:Int -> xs:[Int] -> {v:[Int] | sum v = x + sum xs}
```

But what if our list is polymorphic `[a]` and later instantiate to list of ints?
The workaround we have right now is to strengthen the polymorphic list with the 
`sum` information

```
    [] :: {v:[a] | sum v = 0 }
    (:) :: x:a -> xs:[a] -> {v:[a] | sum v = x + sum xs}
```

But for non numeric `a`s, refinements like `x + sum xs` are ill-sorted! 

We use the flag `--prune-unsorted` to prune away unsorted expressions 
(like `x + sum xs`) inside refinements.


```
    liquid --prune-unsorted test.hs
```


Case Expansion
-------------------------

By default LiquidHaskell expands all data constructors to the case statements.
For example,
if `F = A1 | A2 | .. | A10`,
then LiquidHaskell will expand the code
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
and multiplication as uninterpreted functions use the `linear` flag

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


#### Class Laws

Class laws can be defined and checked using the `class laws` 
and `instance laws` keywords. For an example, see: 

* [class-laws/pos/SemiGroup.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/06d22aa070933d9ea833e30d84ed91de2a28eaee/tests/class-laws/pos/SemiGroup.hs)
* [class-laws/pos/SemiGroup.hs](tests/class-laws/pos/SemiGroup.hs)

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

Forexample,  the length of a list cannot be negative

    {-@ invariant {v:[a] | (len v >= 0)} @-}

LiquidHaskell can prove that this invariant holds, by proving that all List's
constructors (ie., `:` and `[]`) satisfy it.(TODO!) Then, LiquidHaskell
assumes that each list element that is created satisfies
this invariant.

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
  See the [slides directory](docs/slides) for an example.

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

Gipeda will generate a static webpage that tracks the performance improvements
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
for each commit. It is suggested to provide a manageable range to `generate-site.bash`:

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

Updating GHC
============

Here's a script to generate the diff for the `desugar` modules.

```
export GHCSRC=$HOME/Documents/ghc

# Checkout GHC-8.2.2
(cd $GHCSRC && git checkout ghc-8.2.2 && git pull)

# make a patch
diff -ur $GHCSRC/compiler/deSugar src/Language/Haskell/Liquid/Desugar > liquid.patch

# Checkout GHC-8.4.3
(cd $GHCSRC && git checkout ghc-8.2.2 && git pull)

# Copy GHC desugarer to temporary directory
cp -r $GHCSRC/compiler/deSugar .

# Patch
(cd deSugar && patch -p5 --merge --ignore-whitespace < ../liquid.patch)

# Copy stuff over
for i in src/Language/Haskell/Liquid/Desugar/*.*; do j=$(basename $i); echo $j; cp deSugar/$j src/Language/Haskell/Liquid/Desugar; done
```


Here's the magic diff that we did at some point that we keep bumping up to new GHC versions:

https://github.com/ucsd-progsys/liquidhaskell/commit/d380018850297b8f1878c33d0e4c586a1fddc2b8#diff-3644b76a8e6b3405f5492d8194da3874R224 

Warnings
========

Liquid Haskell provides the following warnings:

- `--Wdetect-unsafe` warns if your program includes any unsafe functionality, including `undefined`, `lazy`, or `assume`. Liquid Haskell will admit such functionality even if the implementation is not correct. Disable with `--Wno-detect-unsafe`.
- `--Werror` makes warnings fatal. 

