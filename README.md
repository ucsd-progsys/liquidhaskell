Building and Running
====================

Requirements
-------------

LiquidHaskell requires (in addition to the Hackage dependencies)

- a recent OCaml compiler
- the GNU multiprecision library
- the CamlIDL library

Due to the Z3 dependency, LiquidHaskell can **only be compiled on Linux** at the moment.

How To Clone, Build and Install
-------------------------------

To begin building, run the following commands in the root
directory of the distribution:

1. Create top-level project directory

    mkdir /path/to/liquid
    cd /path/to/liquid
    hsenv
    source .hsenv/bin/activate

2. Install liquid-fixpoint

    git clone git@github.com:ucsd-progsys/liquid-fixpoint.git
    cd liquid-fixpoint
    cabal install
    cd ../

3. Install liquidhaskell

    git clone git@github.com:ucsd-progsys/liquidhaskell.git
    cd liquidhaskell
    cabal install
    cd ../

4. Add to your environment

    LIQUIDHS=/path/to/liquid/liquidhaskell
    export LIQUIDHS

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

    tests/regrtest.py

For example, to run the tests with a particular SMT solver

    ./regrtest.py -t 30 -o "--smtsolver=z3"


How to Profile 
--------------

1. Build with profiling on

    `$ make pdeps && make prof`

2. Run with profiling

    `$ time liquid range.hs +RTS -hc -p`

    `$ time liquid range.hs +RTS -hy -p`

   Followed by this which shows the stats file 

    `$ more liquid.prof`

   or by this to see the graph

    `$ hp2ps -e8in -c liquid.hp`

    `$ gv liquid.ps`

   etc.

How to Get Stack Traces On Exceptions 
-------------------------------------

1. Build with profiling on

    `$ make pdeps && make prof`

2. Run with backtraces

    `$ liquid +RTS -xc -RTS foo.hs`

How to deploy Web Demo
----------------------

1. Set $packagedir in web/liquid.php to a suitable package directory, e.g.
    
    $packagedir = "/home/rjhala/.ghc/x86_64-linux-7.4.1/package.conf.d/";`

2. Name target directory $(SERVERHOME) in Makefile

3. Create target directory

    mkdir $(SERVERHOME)

3. Build and copy files

    make site

4. Set permissions to allow www-data to write to relevant directories

    make siteperms 

The last step requires sudo access which is tedious and should be fixed.

Ignore False Predicates
-----------------------

To ignore false predicates use the nofalse option
 
    liquid --nofalse test.hs

See <a url="tests/neg/lazy.lhs">tests/neg/lazy.lhs</a>

Prune Unsorted Predicates
-----------------------

By default unsorted predicates are pruned.
To disable this behaviour use no-prune-unsorted flag.
 
    liquid --no-prune-unsorted test.hs

Termination Check
-----------------

A termination check is performed on all recursive functions.

Use the `termination-check` option to enable the check
 
    liquid --termination-check test.hs

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

    {-@ Decreasing foo 3 @-}

tells LiquidHaskell to instead use the *third* argument. 

To *disable* termination checking for `foo` that is, to *assume* that it 
is terminating (possibly for some complicated reason currently beyond the 
scope of LiquidHaskell) you can write

    {-@ Strict foo @-} 
    

**Limitations**

- Currently the termination checker *does not* handle *mutually recursive* 
  functions, and instead it loudly crashes when given such functions.

- `deriving instances` often create such functions so lookout!

We intend to address these ASAP.


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

Modules WITH code: Functions 
----------------------------

Write the specification directly into the .hs or .lhs file, 
above the function definition. For example (tests/pos/spec0.hs)

    {-@ incr :: x:{v: Int | v > 0} -> {v: Int | v > x} @-}
    incr   :: Int -> Int
    incr x = x + 1


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

The easiest way to use such self-invariants or refinements, is to just define a type 
alias (e.g. `IList` or `IMaybe` and use them in the specification and verification.)


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


