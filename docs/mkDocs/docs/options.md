# Options and Pragmas

LiquidHaskell supports several command line options, to configure the
checking. 

To see all options, run `liquid --help`. 

Each option can be passed in at the command line, or directly
added to the source file via a **pragma**

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

Below, we list the various options and what they are used for. 

## Theorem Proving 

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


## Fast Checking

The option `--fast` or `--nopolyinfer` greatly recudes verification time, can also reduces precision of type checking. 
It, per module, deactivates inference of refinements during 
instantiation of polymorphic type variables. 
It is suggested to use on theorem proving style when reflected 
functions are trivially refined. 

## Incremental Checking

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


## Full Checking (DEFAULT)

To force LiquidHaskell to check the **whole** file (DEFAULT), use:

    $ liquid --full foo.hs

to the file. This will override any other `--diff` incantation
elsewhere (e.g. inside the file.)


If you always want to run a given file with full-checking, add
the pragma:

    {-@ LIQUID "--full" @-}

## Specifying Different SMT Solvers

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


## Short Error Messages

By default, subtyping error messages will contain the inferred type, the
expected type -- which is **not** a super-type, hence the error -- and a
context containing relevant variables and their type to help you understand
the error. If you don't want the above and instead, want only the
**source position** of the error use:

    --short-errors

## Short (Unqualified) Module Names

By default, the inferred types will have fully qualified module names.
To use unqualified names, much easier to read, use:

    --short-names

## Disabling Checks on Functions

You can _disable_ checking of a particular function (e.g. because it is unsafe,
or somehow not currently outside the scope of LH) by using the `ignore` directive.

For example,

```haskell
{-@ ignore foo @-}
```

will _disable_ the checking of the code for the top-level binder `foo`.

See `tests/pos/Ignores.hs` for an example.


## Totality Check

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

## Termination Check

By **default** a termination check is performed on all recursive functions.

Use the `--no-termination` option to disable the check

    {-@ LIQUID "--no-termination" @-}

See the [specifications documentation][specifications] for how to write termination 
specifications.


## Total Haskell

LiquidHaskell provides a total Haskell flag that checks both totallity and termination of the program,
overriding a potential no-termination flag.

    liquid --total-Haskell test.hs


## Lazy Variables

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

## No measure fields

When a data type is refined, Liquid Haskell automatically turns the data constructor fields into measures.
For example,

    {-@ data L a = N | C {hd :: a, tl :: L a} @-}

will automatically create two measures `hd` and `td`.
To deactivate this automatic measure definition, and speed up verification, you can use the `no-measure-fields` flag.

    liquid --no-measure-fields test.hs



## Prune Unsorted Predicates

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


## Case Expansion

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
The `no-case-expand` flag prevents this expansion and keeps the user
provided cases for the case expression.

    liquid --no-case-expand test.hs


## Higher order logic

The flag `--higherorder` allows reasoning about higher order functions.


## Restriction to Linear Arithmetic

When using `z3` as the solver, LiquidHaskell allows for non-linear arithmetic:
division and multiplication on integers are interpreted by `z3`. To treat division
and multiplication as uninterpreted functions use the `linear` flag

    liquid --linear test.hs

## Counter examples (Experimental!)

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
  See the [slides directory](docs/slides) for an example.
