LiquidHaskell [![Build Status](https://travis-ci.org/ucsd-progsys/liquidhaskell.svg?branch=master)](https://travis-ci.org/ucsd-progsys/liquidhaskell)
=============

Requirements
------------

LiquidHaskell requires (in addition to the cabal dependencies)

- SMTLIB2 compatible solver

How To Clone, Build and Install
-------------------------------


To begin building, run the following commands in the root
directory of the distribution:


1. Install a suitable smt solver binary, e.g.

    + [Z3](http://z3.codeplex.com/)
    + [CVC4](http://cvc4.cs.nyu.edu/) 
    + [MathSat](http://mathsat.fbk.eu/download.html)

   **IMPORTANT**: if you're on Windows, please make sure the solver
   is installed in the **same** directory as LiquidHaskell itself
   (i.e. whereever cabal puts your binaries).

2. Create top-level project directory and clone repositories:

    ```
    mkdir /path/to/liquid
    cd /path/to/liquid
    git clone git@github.com:ucsd-progsys/liquid-fixpoint.git
    git clone git@github.com:ucsd-progsys/liquidhaskell.git
    cd liquidhaskell
    cabal sandbox init
    cabal sandbox add-source ../liquid-fixpoint/
    ```

3. Install 

    ```
    cabal install
    ```

To **rebuild** after this step, run

    `make` or `cabal install`

inside

    /path/to/liquid/liquidhaskell/

How To Run
----------

To verify a file called `foo.hs` at type

    $ liquid foo.hs


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

    $ make pdeps && make prof

2. Run with profiling

    $ time liquid range.hs +RTS -hc -p

    $ time liquid range.hs +RTS -hy -p

   Followed by this which shows the stats file 
    
    $ more liquid.prof

   or by this to see the graph

    $ hp2ps -e8in -c liquid.hp

    $ gv liquid.ps

   etc.

How to Get Stack Traces On Exceptions 
-------------------------------------

1. Build with profiling on

    $ make pdeps && make prof

2. Run with backtraces

    $ liquid +RTS -xc -RTS foo.hs


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
tests/pos/mutrec.hs for the full example).

Lazy Variables
--------------

A variable cab be specified as `LAZYVAR`

    {-@ LAZYVAR z @-}

With this annotation the definition of `z` will be checked at the points where
it is used. For example, with the above annotation the following code is SAFE:

    foo = if x > 0 then z else x
      where z = 42 `safeDiv` x
            x = choose 0

By default, all the variables starting with `fail` are marked as LAZY, to defer
failing checks at the point where these variables are used.

Prune Unsorted Predicates
-------------------------

By default unsorted predicates are pruned away (yielding `true` 
for the corresponding refinement.) To disable this behaviour 
use the `no-prune-unsorted` flag.
 
    liquid --no-prune-unsorted test.hs



Ignore False Predicates
-----------------------

[PLEASE EDIT: I have no idea what "ignoring false predicates means"]

To ignore false predicates use the nofalse option
 
    liquid --nofalse test.hs

See <a url="tests/neg/lazy.lhs">tests/neg/lazy.lhs</a>




Writing Specifications
======================

Modules WITHOUT code
--------------------

For a module Foo.Bar.Baz the spec file is

    include/Foo/Bar/Baz.spec

See, for example, the contents of

    include/Prelude.spec
    include/Data/List.spec
    include/Data/Vector.spec

Modules WITH code: Data
-----------------------

Write the specification directly into the .hs or .lhs file, 
above the data definition. See, for example, `tests/pos/Map.hs`

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
together with the types. For example see (tests/pos/record0.hs)

    {-@ data LL a = BXYZ { size  :: {v: Int | v > 0 }
                         , elems :: {v: [a] | (len v) = size }
                         }
    @-}
    
Finally you can specify the variance of type variables for data types.
For example [see](tests/pos/Variance.hs), where data type `Foo` has four 
type variables `a`, `b`, `c`, `d`, specified as invariant, bivariant, 
covariant and contravariant, respectively.
   
   data Foo a b c d
   {-@ data variance Foo invariant bivariant covariant contravariant @-}


Modules WITH code: Functions 
----------------------------

Write the specification directly into the .hs or .lhs file, 
above the function definition. For example (tests/pos/spec0.hs)

    {-@ incr :: x:{v: Int | v > 0} -> {v: Int | v > x} @-}
    incr   :: Int -> Int
    incr x = x + 1

Modules WITH code: Type Classes
---------------------------------------

Write the specification directly into the .hs or .lhs file, 
above the type class definition. For example (tests/pos/Class.hs)

    {-@ class Sized s where
          size :: forall a. x:s a -> {v:Int | v = (size x)}
    @-}
    class Sized s where
      size :: s a -> Int

Any measures used in the refined class definition will need to be
*generic* (see [Specifying Measures](#specifying-measures)).


As an alternative, you can refine class instances. 
For example (tests/pos/LiquidClass.hs)

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

    [see](tests/pos/ListSort.hs)

and:

    {-@ assert insert :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}

    [see](tests/pos/Map.hs)

**Syntax:** The key requirements for type aliases are:

1. Type parameters are specified in **lower**case: `a`, `b`, `c` etc.
2. Value parameters are specified in **upper**case: `X`, `Y`, `Z` etc.




Specifying Measures
-------------------

Can be placed in .spec file or in .hs/.lhs file wrapped around {-@ @-}

Value measures (include/GHC/Base.spec)

    measure len :: forall a. [a] -> GHC.Types.Int
    len ([])     = 0
    len (y:ys)   = 1 + len(ys)


Propositional measures (tests/pos/LambdaEval.hs)

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

Raw measures (tests/pos/meas8.hs)

    {-@ measure rlen :: [a] -> Int 
    rlen ([])   = {v | v = 0}
    rlen (y:ys) = {v | v = (1 + rlen(ys))}
    @-}


Generic measures (tests/pos/Class.hs)

    {-@ class measure size :: a -> Int @-}
    {-@ instance measure size :: [a] -> Int
        size ([])   = 0
        size (x:xs) = 1 + (size xs)
    @-}
    {-@ instance measure size :: Tree a -> Int
        size (Leaf)       = 0
        size (Node x l r) = 1 + (size l) + (size r)
    @-}


Haskell Functions as Measures (beta) (tests/pos/HaskellMeasure.hs)

Inductive Haskell Functions from Data Types to some type can be lifted to logic
    {-@ measure llen @-}

    llen        :: [a] -> Int
    llen []     = 0
    llen (x:xs) = 1 + llen xs

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
There are two ways of specifying invariants in LiquidHaskell.
First, there are *global* invariants that always hold for a data-type. For
example,  the length of a list cannot be negative

    {-@ invariant {v:[a] | (len v >= 0)} @-}

LiquidHaskell can prove that this invariant holds, by proving that all List's
constractos (ie., `:` and `[]`) satisfy it.(TODO!)
Then, LiquidHaskell assumes that each list element that is created satisfies
this invariant.

Second, there are *local* invariants that one may use. For
example, in [test/pos/StreamInvariants.hs](tests/pos/StreamInvariants.hs) every
list is treated as a Stream. To establish this local invariant one can use the
`using` declaration

    {-@ using ([a]) as  {v:[a] | (len v > 0)} @-}

denoting that each list is not empty.
Then, LiquidHaskell will prove that this invariant holds, by proving that *all
calls* to List's
constractos (ie., `:` and `[]`) satisfy it, and
will assume that each list element that is created satisfies
this invariant.

With this, at the [above](tests/neg/StreamInvariants.hs) test LiquidHaskell
proves that taking the `head` of a list is safe.
But, at [test/neg/StreamInvariants.hs](tests/neg/StreamInvariants.hs) the usage of
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


