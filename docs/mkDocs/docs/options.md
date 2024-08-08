# Options and Pragmas

LiquidHaskell supports several configuration options, to alter the type checking.

You can pass options in different ways:

1. As a **pragma**, directly added to the source file: **(recommended)**

        {-@ LIQUID "--opt1" @-}

2. As a **plugin option**:

        ghc-options: -fplugin-opt=LiquidHaskell:--opt1 -fplugin-opt=LiquidHaskell:--opt2

3. In the **environment variable** `LIQUIDHASKELL_OPTS` (e.g. in your `.bashrc` or `Makefile`):

        LIQUIDHASKELL_OPTS="--opt1 --opt2"

4. From the **command line**, if you use the **legacy executable**:

        liquid --opt1 --opt2 ...

The options are descibed below (and by the legacy executable: `liquid --help`)

## Theorem Proving

**Options:** `reflection`, `ple`, `ple-local`, `extensionality`, `ple-with-undecided-guards`, `--dump-opaque-reflections`

**Directives:** `automatic-instances`

To enable theorem proving, e.g. as [described here](tags.html#reflection)
use the option

```haskell
    {-@ LIQUID "--reflection" @-}
```

To additionally turn on _proof by logical evaluation_ (PLE) use the option

```haskell
    {-@ LIQUID "--ple" @-}
```

You can see many examples of proofs by logical evaluation in `tests/benchmarks/popl18/ple/pos`

This flag is **global** and will symbolically evaluate all the terms that appear in the specifications.

As an alternative, the `--ple-local` flag has local behavior. [See](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/benchmarks/popl18/ple/pos/Unification.hs)

```
{-@ LIQUID "--ple-local" @-}
```

will only evaluate terms appearing in the specifications
of the function `theorem`, if the function `theorem` is
annotated for automatic instantiation using the following
liquid annotation

```
{-@ automatic-instances theorem @-}
```

Normally, PLE will only unfold invocations only if the arguments are known
with enough precision to enter some of the equations of the function. For
instance, in

```Haskell
{-@ reflect boolToInt @-}
boolToInt :: Bool -> Int
boolToInt False = 0
boolToInt True = 1

{-@ nonNegativeInt :: b:_ -> { boolToInt b >= 0 } @-}
nonNegativeInt :: Bool -> ()
nonNegativeInt _ = ()
```

the equations `boolToInt False = 0` and `boolToInt True = 1` would only be
used if `b` is known to be either `True` or `False`. Now, if nothing is
known about `b` and we still would like to use the fact that

```Haskell
boolToInt b = if b then 1 else 0
```

we can instruct Liquid Haskell to do so and accept `nonNegativeInt` with

```
{-@ LIQUID "--ple-with-undecided-guards" @-}
```

`--ple-with-undecided-guards` causes all invocations that haven't been unfolded
due to undecided guards to be unfolded at the end of the algorithm.
Alternatively, one could selectively unfold the invocations of some particular
function only with `Language.Haskell.Liquid.ProofCombinators.pleUnfold`.

```
boolToInt b = pleUnfold (if b then 1 else 0)
```

Now, PLE will unfold `boolToInt` as above every time `b` is undecided. But won't
unfold any other invocations with undecided guards unless they also start with an
application of `pleUnfold`.

To allow reasoning about function extensionality use the `--extensionality` flag.
[See test T1577](https://github.com/ucsd-progsys/liquidhaskell/blob/880c78f94520d76fa13880eac050f21dacb592fd/tests/pos/T1577.hs).

```
{-@ LIQUID "--extensionality" @-}
```

Furthermore, you may also want to assume the reflection of some functions that you haven't defined,
but need in your own reflected functions, or in the logic. For instance, let's say that you want to
define the following function:

```Haskell
{-@ reflect keepDigits @-}
keepDigits :: [Char] -> [Char]
keepDigits = filter isDigit
```

Or that you want to prove a property of filter:

```Haskell
{-@ lemma :: {v:[Char] | v == []} @-}
lemma::  [Char]
lemma = filter isDigit []
```

Both will fail because `GHC.List.filter` was not reflected in the first place, nor was `isDigit`. To overcome the problem,
you can assume the reflection of both functions by defining a *pretended* function that should behave in the same way
as the actual function. Therein lies the assumption: if both functions don't actually behave in the same way, then you
may introduce falsity in your logic. Thus, you have to use it with caution, only when the function wasn't already reflected,
and when you actually know how it will behave. In the following snippet, `myfilter` is the pretended function whose definition
is given in our module, and the actual function `GHC.List.filter` and `myfilter` and tied through 
the `{-@ assume reflect filter as myfilter @-}` annotation. This annotation must be read as: "reflect `filter`, assuming it has the 
same reflection as `myfilter`".

```Haskell
-- Reflect filter
{-@ reflect myfilter @-}
{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a] | len xs >= len v} @-}
myfilter :: (a -> Bool) -> [a] -> [a]
myfilter _pred []	= []
myfilter pred (x:xs)
  | pred x     	= x : myfilter pred xs
  | otherwise  	= myfilter pred xs

{-@ assume reflect filter as myfilter @-}

-- Reflect isDigit

{-@ reflect myIsDigit @-}
myIsDigit :: Char -> Bool
myIsDigit x = '0' <= x && x <= '9'

{-@ assume reflect isDigit as myIsDigit @-}
```

### Opaque reflection

LH automatically introduces uninterpreted functions / measures for all symbols which appear in the expression to reflect,
but which are not already defined in the refinement logic. However, if you want to see exactly which symbols will be *opaque-reflected*
(that's the term for it), you use this pragma:

```Haskell
{-@ LIQUID "--dump-opaque-reflections" @-}
```

It will dump the list of opaque reflections to the output. For example, assuming that `GHC.Internal.List.filter`
and `GHC.Internal.Real.even` are not reflected, we get the following output for the following snippet.

```Haskell
{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--dump-opaque-reflections"      @-}

module OpaqueRefl06 where

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
```

```
Opaque reflections:
- GHC.Internal.List.filter
- GHC.Internal.Real.even
```


Note: you can also reflect functions *away* from their definition, using interface files. For instance, you may do:

```Haskell
{-@ reflect uncurry @-}

{-@ reflect otherFn @-}
otherFn :: (Int , Int) -> Int
otherFn = uncurry myAdd

{-@ reflect myAdd @-}
myAdd :: Int -> Int -> Int
myAdd a b = a + b + 1
```

Even though `uncurry` is an external, imported symbol.

For this, LH will go and fetch the *unfoldings* of the function, which is essentially its content that is also used when the compiler does
inlining.
The unfoldings of these functions must be available, which is not always the case. Also note that even when they are available,
not all functions can be reflected, for the same reasons as some of your own functions may not be reflected (presence of recursive definitions,
 for instance).

If the reflection of these happen to need the reflection of private variables inside those modules, you can also request their reflection
with another `reflect` annotation with the _fully-qualified_ name of the private variable to reflect, i.e. something like:

```
{-@ reflect MyMod.privFn @-}
```

Note: reflection of private variables only work if these variables occur in the definition of other variables that could already be reflected.
You cannot reflect a private variable in general otherwise.
Note 2: if these private variables are not manually reflected by you, they are, as usual, opaque-reflected automatically, as you can see
by dumping the opaque reflections.

## Fast Checking

**Options:** `fast`, `nopolyinfer`

The option `--fast` or `--nopolyinfer` greatly recudes verification time, can also reduces precision of type checking.
It, per module, deactivates inference of refinements during
instantiation of polymorphic type variables.
It is suggested to use on theorem proving style when reflected
functions are trivially refined.

## Incremental Checking

**Options:** `diff`

The LiquidHaskell executable supports *incremental* checking where each run only checks
the part of the program that has been modified since the previous run. Each run of `liquid` saves the file
to a `.bak` file and the *subsequent* run does a `diff` to see what has changed w.r.t. the `.bak` file only
generates constraints for the `[CoreBind]` corresponding to the changed top-level binders and their
transitive dependencies.

The time savings are quite significant. For example:

```
    $ time liquid --notermination -i . Data/ByteString.hs > log 2>&1

    real	7m3.179s
    user	4m18.628s
    sys	    0m21.549s
```

Now if you go and tweak the definition of `spanEnd` on line 1192 and re-run:

```
    $ time liquid --diff --notermination -i . Data/ByteString.hs > log 2>&1

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

## Full Checking (DEFAULT)

**Options:** `full`

You can force LiquidHaskell to check the **whole** file (which is the _DEFAULT_) using the `--full` option.
This will override any other `--diff` incantation elsewhere (e.g. inside the file). If you always want
to run a given file with full-checking, add the pragma:

    {-@ LIQUID "--full" @-}

## Specifying Different SMT Solvers

**Options:** `smtsolver`

By default, LiquidHaskell uses the SMTLIB2 interface for Z3.

To run a different solver (supporting SMTLIB2) do:

    $ liquid --smtsolver=NAME foo.hs

Currently, LiquidHaskell supports

+ [CVC4](http://cvc4.cs.stanford.edu/web/)
+ [MathSat](http://mathsat.fbk.eu/download.html )

To use these solvers, you must install the corresponding binaries
from the above web-pages into your `PATH`.

## Short Error Messages

**Options:** `short-errors`

By default, subtyping error messages will contain the inferred type, the
expected type -- which is **not** a super-type, hence the error -- and a
context containing relevant variables and their type to help you understand
the error. If you don't want the above and instead, want only the
**source position** of the error use `--short-errors`.

## Short (Unqualified) Module Names

**Options:** `short-names`

By default, the inferred types will have fully qualified module names.
To use unqualified names, much easier to read, use `--short-names`.

## Disabling Checks on Functions

**Directives:** `ignore`

You can _disable_ checking of a particular function (e.g. because it is unsafe,
or somehow not currently outside the scope of LH) by using the `ignore` directive.

For example,

```haskell
{-@ ignore foo @-}
```

will _disable_ the checking of the code for the top-level binder `foo`.

See `tests/pos/Ignores.hs` for an example.


## Totality Check

**Options:** `no-totality`

LiquidHaskell proves the absence of pattern match failures.

For example, the definition

```haskell
fromJust :: Maybe a -> a
fromJust (Just a) = a
```

is not total and it will create an error message.
If we exclude `Nothing` from its domain, for example using the following specification

```haskell
{-@ fromJust :: {v:Maybe a | (isJust v)} -> a @-}
```

`fromJust` will be safe.

Use the `no-totality` flag to disable totality checking.

## Termination Check

**Options:** `no-termination`

By **default** a termination check is performed on all recursive functions, but you can disable the check
with the `--no-termination` option.

See the [specifications section](specifications.md) for how to write termination specifications.

## Positivity Check

**Options:** `no-positivity-check`
By **default** a positivity check is performed on data definitions. 


```haskell
data Bad = Bad (Bad -> Bad) | Good Bad 
    --           A      B           C
    -- A is in a negative position, B and C are OK
```

Negative declarations are rejected because they admit non-terminating functions.

If the positivity check is disabled, so that a similar declaration of `Bad` is allowed, 
it is possible to construct a term of the empty type, even without recursion.
For example see [tests/neg/Positivity1.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/errors/Positivity1.hs)
and [tests/neg/Positivity2.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/errors/Positivity2.hs)

```haskell
data Evil a = Very (Evil a -> a)

{-@ type Bot = {v: () | false} @-}

{-@ bad :: Evil Bot -> Bot @-}
bad :: Evil () -> ()
bad (Very f) = f (Very f)

{-@ worse :: Bot @-}
worse :: ()
worse = bad (Very bad)
```

Note that all positive occurrences are permited, unlike Coq that only allows the strictly positive ones
(see: https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/)

## Total Haskell

**Options:** `total-Haskell`

LiquidHaskell provides a total Haskell flag that checks both totallity and termination of the program,
overriding a potential no-termination flag.

## Lazy Variables

A variable can be specified as `LAZYVAR`

    {-@ LAZYVAR z @-}

With this annotation the definition of `z` will be checked at the points where
it is used. For example, with the above annotation the following code is SAFE:

```haskell
foo   = if x > 0 then z else x
  where
    z = 42 `safeDiv` x
    x = choose 0
```

By default, all the variables starting with `fail` are marked as LAZY, to defer
failing checks at the point where these variables are used.

## No measure fields

**Options:** `no-measure-fields`

When a data type is refined, Liquid Haskell automatically turns the data constructor fields into measures.
For example,

```haskell
{-@ data L a = N | C {hd :: a, tl :: L a} @-}
```

will automatically create two measures `hd` and `td`. To deactivate this automatic measure definition,
and speed up verification, you can use the `--no-measure-fields` flag.

## Prune Unsorted Predicates

**Options:** `prune-unsorted`

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

## Case Expansion

**Options:** `no-case-expand`

By default LiquidHaskell expands all data constructors to the case statements.
For example, given the definition

```haskell
data F = A1 | A2 | .. | A10
```

LiquidHaskell will expand the code

```haskell
case f of {A1 -> True; _ -> False}
```

to

```haskell
case f of {A1 -> True; A2 -> False; ...; A10 -> False}
```

This expansion can lead to more precise code analysis
but it can get really expensive due to code explosion.
The `--no-case-expand` flag prevents this expansion and keeps the user
provided cases for the case expression.

## Higher order logic

**Options:** `higherorder`

The flag `--higherorder` allows reasoning about higher order functions.

## Restriction to Linear Arithmetic

**Options:** `linear`

When using `z3` as the solver, LiquidHaskell allows for non-linear arithmetic:
division and multiplication on integers are interpreted by `z3`. To treat division
and multiplication as uninterpreted functions use the `--linear` flag.

## Counter examples

**Options:** `counter-examples`

**Status:** `experimental`

When given the `--counter-examples` flag, LiquidHaskell will attempt to produce
counter-examples for the type errors it discovers. For example, see
[tests/neg/ListElem.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/neg/ListElem.hs)

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

## Typeclasses

**Options:** `typeclass`

**Status:** `experimental`

The `--typeclass` flag enables LiquidHaskell's support of
typeclasses. One limitation is that proofs cannot be written directly
within the instance definition unless the `--aux-inline` flag is
turned on as well.

## Generating HTML Output

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
  See the [slides directory](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/docs/slides) for an example.


## Loading specifications automatically

By default, Liquid Haskell will load the specifications from module
`A.B.C_LHAssumptions` whenever it finds an import of module `A.B.C`.
For instance,

```Haskell
import Data.Vector
import Data.Vector.Unboxed
```

would cause Liquid Haskell to try modules `Data.Vector_LHAssumptions`
and `Data.Vector.Unboxed_LHAssumptions`. If the `_LHAssumptions` module
is missing, vecrification proceeds without any extra specifications.

`A.B.C_LHAssumptions` is looked in any package that is visible to GHC
when verifying a module. But the following flag can be used to stop
this automatic loading when the imported module belongs to the given
package.

**Options:** `--exclude-automatic-assumptions-for=PACKAGE`

Liquid Haskell will not load `_LHAssumptions` modules upon finding
an import of a module coming from package `PACKAGE`. e.g.
`--exclude-automatic-assumptions-for=vector` would stop loading
`_LHAssumptions` modules for any imports coming from package
`vector`.
