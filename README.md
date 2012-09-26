Building and Running 
====================

Requirements
-------------

LiquidHaskell requires (in addition to the Hackage dependencies)

- a recent OCaml compiler
- the GNU multiprecision library
- the CamlIDL library

Due to the Z3 dependency, LiquidHaskell can **only be compiled on Linux** at the moment.

How to Clone
------------

To clone liquidhaskell:

    git clone git@github.com:ucsd-progsys/liquidhaskell.git

How To Build and Install
------------------------

To begin building, run the following commands in the root
directory of the distribution:

1. Run the `configure` script

    `$ ./configure`

2. Run the generated `build` script

    `$ ./build.sh`

3. Append the contents of the generated `install.sh` to your `.bashrc`
   (or set the corresponding environment variables appropriately)

To **rebuild** after this step, just do

    make


How To Run
----------

To verify a file called `foo.hs` at type

    $ liquid foo.hs


How To Run Regression Tests 
---------------------------

    $ make test

To use threads to speed up the tests

    $ make THREADS=30 test

or your favorite number of threads, depending on cores etc.


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

How to Get Backtraces
---------------------

1. Build with profiling on

    `$ make pdeps && make prof`

2. Run with backtraces

    `$ liquid +RTS -xc -RTS foo.hs`


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

Modules WITH code: Functions 
----------------------------

Write the specification directly into the .hs or .lhs file, 
above the function definition. For example (tests/pos/spec0.hs)

    {-@ incr :: x:{v: Int | v > 0} -> {v: Int | v > x} @-}
    incr   :: Int -> Int
    incr x = x + 1


Refinement Type Aliases
-----------------------

TODO:

It is often tedious to keep writing 

    {v: Int | v > 0}

Thus, one can have refinement-type aliases of the form:

    {-@ reftype PosInt = {v: Int | v > 0} @-}

or

    {-@ reftype SortedList a = [a]<{v: a | (v >= fld)}> @-}

or 

    {-@ reftype OMap k a = Map <{v: k | v < key}, {v: k | v > key}> k a @-}
   
and then use the above in signatures like:

    {-@ assert insert :: (Ord a) => a -> SortedList a -> SortedList a @-}

    (tests/pos/ListSort.hs)

and:

    {-@ assert insert :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}

    (tests/pos/Map.hs)


Specifying Qualifiers
---------------------

Qualifier files must end with extension .hquals

You can write qualifier files (see include/Prelude.hquals for an example)

If a module is called or imports 

    Foo.Bar.Baz

Then the system automatically searches for

    include/Foo/Bar/Baz.hquals

Additional qualifiers may be used by adding lines of the form:

    {-@ include <path/to/file.hquals> @-}

to the Haskell source. See, for example, `tests/pos/meas5.hs` 

Generating HTML Output
======================

The system produces HTML files with colorized source, and mouseover 
inferred type annotations, which are quite handy for debugging failed 
verification attempts.

- **Regular Haskell** When you run: `liquid foo.hs` you get a file 
  `foo.hs.html` with the annotations. The coloring is done using
  `hscolour`.

- **Markdown + Literate Haskell** You can also feed in literate haskell files
  where the comments are in [Pandoc markdown](http://johnmacfarlane.net/pandoc/demo/example9/pandocs-markdown.html). In this case, the tool will run `pandoc` to generate the HTML from the comments.
  Of course, this requires that you have `pandoc` installed as a binary on
  your system. If not, `hscolour` is used to render the HTML.


