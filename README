How To Compile
--------------

Set GHCHOME in config.make.0

  $ cp config.make.0 config.make
  $ make deps && make

How To Run 
----------
  
1. add this to .bashrc

LIQUIDHS=PATH/TO/LiquidHaskell/cabal/include/
export LIQUIDHS

2. ensure "fixpoint.native" is in the executable search path

3. path/to/liquid foo.hs

How To Run Tests 
----------------

  $ make deps && make && make test

To use threads to speed up the tests

  $ make THREADS=30 test

or your favorite number of threads, depending on cores etc.


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

How to Get Backtraces
---------------------

1. Build with profiling on

    $ make pdeps && make prof

2. Run with backtraces

    $ liquid +RTS -xc -RTS foo.hs


Writing Specifications
======================

For modules WITH code
---------------------

Modules WITHOUT code
--------------------

For a module Foo.Bar.Baz the spec file is

    $(INCLUDEDIR)/Foo/Bar/Baz.spec

For example:

    - include/Prelude.spec
    - include/Data/List.spec
    - include/Data/Vector.spec

Modules WITH code: Data
-----------------------

Write the specification directly into the .hs or .lhs file, 
above the data definition. For example (tests/pos/Map.hs)

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

    {-@ assert incr :: x:{v: Int | v > 0} -> {v: Int | v > x} @-}
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

to the Haskell source. See tests/pos/meas5.hs for an example.



