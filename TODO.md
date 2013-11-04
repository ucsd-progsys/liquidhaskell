TODO
====


* Qualified Imports
  - wtf is include/KMeansHelper.hs ? Fix module import issue
  - break spec imports -- tests/todo/qualifiedvector.hs 

* benchmarks: Data.Bytestring
    ? readsPrec
    ? big constants issue : _word64 34534523452134213524525 due to (deriving Typeable)
    - see others below

* hmatrix

* error messages (see issues on github) 

* speed (exists)
  + Data.Vector.Algorithms.Optimal

exists-based constraints
------------------------

("Foo" [x, y]) vs ("App" ["App" [a, b], "c"]


KVar Distribution Optimal.hs:  [LetE : 456, LamE : 309, TypeInstE : 649]


GHC introduces a bunch of:

    let x = e1 in e2

and

    case x of C y -> e

constraints, which possibly blow up the `Kvar`.

Can we minimize KVars and hence, simplify constraints with exists?

1. profile and find the KVar break down.

  + lambda (including recursion)
  + polymorphic instantiation
  + case-of with *multiple* cases
  - case-of with *single* case
  - local-let

2. eliminate the last two cases using exists-templates

vector-algorithms
-----------------

1. array-sum measure needed to discharge liquidAssume in `Radix`

[OK] Compiling Data.Vector.Algorithms.Common
real	0m6.654s
user	0m4.380s
sys	    0m0.384s

[OK] Compiling Data.Vector.Algorithms.Radix
real	0m31.431s
user	0m23.981s
sys	0m1.808s

[OK] Compiling Data.Vector.Algorithms.Search
real	0m13.892s
user	0m9.573s
sys	0m0.788s

[OK] Compiling Data.Vector.Algorithms.Optimal
real	3m36.357s
user	2m54.143s
sys	0m11.585s

[OK] Compiling Data.Vector.Algorithms.Insertion
real	0m16.949s
user	0m12.505s
sys	0m0.832s

[OK] Compiling Data.Vector.Algorithms.Heap
real	2m21.595s
user	1m35.626s
sys	0m6.924s

[OK] Compiling Data.Vector.Algorithms.Merge 
real	0m57.314s
user	0m44.839s
sys	0m2.704s

[OK] Compiling Data.Vector.Algorithms.AmericanFlag
real	1m16.639s
user	0m55.027s
sys	0m3.644s

[OK] Compiling Data.Vector.Algorithms.Intro 

real	1m4.456s
user	0m47.539s
sys	    0m2.552s

AmericanFlag.hs.cgi
[LetE : 142, CaseE : 195, LamE : 336, PredInstE : 10, TypeInstE : 301, RecBindE : 45]

Common.hs.cgi
[LetE : 17, CaseE : 28, LamE : 43, PredInstE : 4, TypeInstE : 50, RecBindE : 5]

Heap.hs.cgi
[LetE : 237, CaseE : 156, LamE : 327, PredInstE : 40, TypeInstE : 331, RecBindE : 20]

Insertion.hs.cgi
[LetE : 51, CaseE : 78, LamE : 82, TypeInstE : 61, RecBindE : 10]

Intro.hs.cgi
[LetE : 112, CaseE : 103, LamE : 142, TypeInstE : 111, RecBindE : 34]

Merge.hs.cgi
[LetE : 99, CaseE : 192, LamE : 126, PredInstE : 15, TypeInstE : 180, RecBindE : 27]

Optimal.hs.cgi
[LetE : 456, LamE : 309, TypeInstE : 649]

Radix.hs.cgi
[LetE : 63, CaseE : 136, LamE : 299, TypeInstE : 123, RecBindE : 20]

Search.hs.cgi
[LetE : 63, CaseE : 72, LamE : 95, TypeInstE : 82, RecBindE : 15]




hmatrix
-------

Dependency order for hmatrix

NA [ 1 of 36] Data.Packed.Internal.Signatures
TY [ 2 of 36] Data.Packed.Internal.Common 
  > see tests/pos/transpose.hs

[ 3 of 36] Data.Packed.Internal.Vector 
[ 4 of 36] Numeric.GSL.Vector 
[ 5 of 36] Data.Packed.Internal.Matrix 
[ 6 of 36] Numeric.Conversion
[ 7 of 36] Data.Packed.Internal
[ 8 of 36] Data.Packed.ST
[ 9 of 36] Data.Packed.Foreign
[10 of 36] Numeric.GSL.Differentiation
[11 of 36] Numeric.GSL.Integration
[12 of 36] Numeric.GSL.Fourier
[13 of 36] Numeric.GSL.Polynomials
[14 of 36] Numeric.GSL.Internal
[15 of 36] Numeric.GSL.ODE
[16 of 36] Data.Packed.Development
[17 of 36] Data.Packed.Matrix
[18 of 36] Numeric.GSL.Minimization
[19 of 36] Numeric.GSL.Root
[20 of 36] Numeric.LinearAlgebra.LAPACK 
[21 of 36] Data.Packed.Vector
[22 of 36] Data.Packed
[23 of 36] Numeric.ContainerBoot
[24 of 36] Numeric.Chain
[25 of 36] Numeric.LinearAlgebra.Algorithms 
[26 of 36] Numeric.IO
[27 of 36] Data.Packed.Random
[28 of 36] Numeric.Container
[29 of 36] Numeric.Matrix
[30 of 36] Numeric.Vector
[31 of 36] Numeric.LinearAlgebra
[32 of 36] Numeric.GSL.Fitting
[33 of 36] Numeric.GSL
[34 of 36] Numeric.LinearAlgebra.Util.Convolution 
[35 of 36] Numeric.LinearAlgebra.Util 
[36 of 36] Graphics.Plot


Embed
=====

see 

    tests/pos/ptr.hs
    tests/pos/ptr2.hs

run with 

    liquid -i include/ -i benchmarks/bytestring-0.9.2.1/ tests/pos/ptr2.hs 

GET THIS TO WORK WITHOUT THE "base" measure and realated theorem,
but with raw pointer arithmetic. I.e. give plusPtr the right signature:
  (v = base + off)
Can do so now, by:

  embed Ptr as int 

but the problem is that then it throws off all qualifier definitions like
 
  qualif EqPLen(v: ForeignPtr a, x: Ptr a): (fplen v) = (plen x)
  qualif EqPLen(v: Ptr a, x: ForeignPtr a): (plen v) = (fplen x) 

because there is no such thing as Ptr a by the time we get to Fixpoint. yuck.
Meaning we have to rewrite the above to the rather lame:

  qualif EqPLenPOLY2(v: a, x: b): (plen v) = (fplen x)           



Benchmarks
==========

                        time(O|N|C)    TOTAL(O|N)   solve (O|N)      refines       iterfreq
    Map.hs          :    54/50/32/10    21/15/8.7      14/8/4.3    9100/4900/2700    16/28/7
    ListSort.hs     :   */7.5/5.5/2    */2.5/1.8     */1.5/1.0      */1100/600       */9/7
    GhcListSort.hs  :    23/22/17/5    7.3/7.8/5   4.5/5.0/2.7    3700/4400/1900   10/23/6
    LambdaEval.hs   :    36/32/25/12    17/12/10     11.7/6.0/5    8500/3100/2400   12/5/5
    Base.hs         :        26mi/2m


Blog Todo List
==============

- Cleanup output (tests/pos/poly0.hs)

Basic Refinement Types
----------------------

[DONE] RefTypes 101  (Basic Ints, abz, div-by-zero)
[DONE] Dep Refinements: (Data.Vector, recursion-sum, dotprod, range, map, fold)
[DONE] Lists I       (append, reverse, map-length, filter)
[DONE] Lists II      (take, transpose)
[DONE] MapReduce
[DONE] KMeans        (++ zipWith etc.)

Measures
--------

[DONE] Lists I-Sets  ("" but with Sets as the measure)
- LambdaEval	

Abstract Refinements
--------------------

[DONE] ParaPoly/Ty  
[DONE] Sorting      <--------------- STOP 

- Maps I        (BST property, add, delete)
- Map II        (Data.Map with elements etc.)
- Pats Vectors
- Niki DataBase
- Induction-Loop
- Induction-List (efoldr)

Real World
----------

- Bytestring (internal)
- Bytestring (api)
- Text       (internal)
- Text       (api)
- Text       (bug)
- Lazy/Termination
- Termination examples
? mcbride stack machine
? hasochism text layout


Future Work
-----------

- Xmonad: StackSet
- Binary Tree/ Finger Tree?
- BDD
- Union Find


Benchmarks
==========

[OK]    Data.KMeans
[OK]    GHC.List   (../benchmarks/ghc-7.4.1/List.lhs)
[OK]    bytestring
[OK]    text

[??-PP] Data.Map (supersedes set)
        - ordering [OK]
        - size
        - key-set-properties
        - key-dependence
        - balance (NO)
        
-   vector-algorithms "vector bounds checking"
      - e.g. "unsafeSlice"
      - maybe only specify types for Vector?

-   vector
-   repa
-   repa-algorithms
- 	xmonad (stackset)
-   snap/security
-   hmatrix
      > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Matrix.html#Matrix
      > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Vector.html#fromList

Other Benchmarks
================

->   FingerTrees (containers / Data.Seq)
->   Union-Find (PLDI09 port if necessary?)
->   BDD        (PLDI09 port if necessary?)


[NO] Data.Set (Map redux)
        > ordering
        > size
        > set-properties
        > balance (NO)

[NO] Data.IntSet
     > tricky bit-level operations/invariants

Paper #2

-> Haskell + DB / Yesod / Snap
-> NDM/catch benchmarks (with refinements)

Known Bugs 
==========

-> tests/todo/fft.hs

-> binsearch crashes because you have chains like:
        
        x1 = 2
        x2 = x1
        x3 = x2
        z  = x3 / 2

  so I guess you need some constprop inside the constraint simplification.

- tests/pos/data-mono0.hs
  partial pattern match desugars into exception syntax with unhandled
  casts. Throws an error in fixpoint. At least throw error in Constraint Gen?
          (\ _ ->
             (Control.Exception.Base.irrefutPatError
                @ () "pos/data-mono0.hs:8:9-23|(Test.Cons x _)")
             `cast` (UnsafeCo () GHC.Types.Int :: () ~ GHC.Types.Int))
            GHC.Prim.realWorld#;


Xmonad Case Study
=================

Theorems (from Wouter Swierstra's Coq Development)

    - Invariant: NoDuplicates

    - prop_empty_I      : new  : ? -> {v | invariant(v)} 
    - prop_view_I       : view : ? -> {v | invariant(v)} 
    - prop_greedyView_I : view : ? -> {v | invariant(v)}
    - prop_focusUp_I
    - prop_focusMaster_I
    - prop_focusDown_I 
    - prop_focus_I 
    - prop_insertUp_I
    - prop_delete_I
    - prop_swap_master_I
    - prop_swap_left_I  
    - prop_swap_right_I
    - prop_shift_I 
    - prop_shift_win_I 

[prop_FOO_I] check that various functions outputs satisfy "invariant"

    FOO :: ??? -> {v: StackSet | invariant(v)}

    > Theorem prop_swap_master_I (s : StackSet.stackSet i l a sd) :
    > Theorem prop_view_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
    > Theorem prop_greedyView_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
    > Theorem prop_focusUp_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
    > Theorem prop_focusDown_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
    > Theorem prop_focusMaster_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
    > Theorem prop_empty_I (m : l) (wids : {wids : list i | wids <> nil}) 
    > Theorem prop_empty (m : l) (wids : {wids : list i | wids <> nil}) 
    > Theorem prop_differentiate (xs : list a) :

[prop_FOO_local] check that various functions preserve a [hidden_spaces] MEASURE 

    FOO :: x: StackSet -> {v: StackSet | hidden_spaces(v) = hidden_spaces(x) }

    > Theorem prop_focus_down_local (s : stackSet i l a sd) :
    > Theorem prop_focus_up_local (s : stackSet i l a sd) : 
    > Theorem prop_focus_master_local (s : stackSet i l a sd) :
    > Theorem prop_delete_local (s : stackSet i l a sd) (eq_dec : forall x y, {x = y} + {x <> y}) :
    > Theorem prop_swap_master_local (s : stackSet i l a sd) : 
    > Theorem prop_swap_left_local (s : stackSet i l a sd) : 
    > Theorem prop_swap_right_local (s : stackSet i l a sd) : 
    > Theorem prop_shift_master_local (s : stackSet i l a sd) : 
    > Theorem prop_insert_local (x : stackSet i l a sd) (eq_dec : forall x y, {x = y} + {x <> y}) :


BAD: these check that: forall x: foo (bar x) == x

    > Theorem prop_focus_right (s : StackSet.stackSet i l a sd) :
    > Theorem prop_focus_left (s : StackSet.stackSet i l a sd) :

[prop_swap_*_focus] check that various functions preserve a [peek] MEASURE
    > Theorem prop_swap_master_focus (x : StackSet.stackSet i l a sd) :
    > Theorem prop_swap_left_focus (x : StackSet.stackSet i l a sd) :
    > Theorem prop_swap_right_focus (x : StackSet.stackSet i l a sd) :


BAD? forall x. swapMaster (swapMaster x) == x 
    > Theorem prop_swap_master_idempotent (x : StackSet.stackSet i l a sd) : 
    
BAD? forall x. view i (view i x) == (view i x)
    > Theorem prop_focusMaster_idem (x : StackSet.stackSet i l a sd) :

    NO. Prove: view :: i -> x -> {v: focus(v) = i}
                    :: i -> x -> {v: focus(x) = i => x = v } 
        
    To prove foo_IDEMPOTENT, find a property P such that:

                foo :: x:t -> {v:t | P(v)}
                foo :: x:t -> {v:t | P(x) => v = x }

SETS: 
    > Theorem prop_screens (s : stackSet i l a sd) :


TRIV/HARD: (function definition)
    > [TRIV]  Theorem prop_screens_work (x : stackSet i l a sd) :
    > Theorem prop_mapWorkspaceId (x : stackSet i l a sd) : 
    > Theorem prop_mapLayoutId (s : stackSet i l a sd) :
    > Theorem prop_mapLayoutInverse (s : stackSet i nat a sd) :
    > Theorem prop_mapWorkspaceInverse (s : stackSet nat l a sd) :

Theorem prop_lookup_current (x : stackSet i l a sd) :
Theorem prop_lookup_visible (x : stackSet i l a sd) : 


Random Links
============

- Useful for DIGRAPH VIZ: http://arborjs.org/halfviz/#


GITTERY
=======

To make local branch `goo`

    $ git branch foo
    $ git checkout foo
    $ ...
    $ git commit -a -m "did work in foo"

To send branch to the mothership

    $ git push origin foo

To work with branch elsewhere

    $ git pull
    $ git checkout foo

Benchmark Tags
==============

- LIQUIDFAIL : impossible to do verify the spec here
- LIQUIDTODO : possible with some further hacking



----------------------------------------------------------------------------

http://www.cs.st-andrews.ac.uk/~eb/writings/fi-cbc.pdf

McBride's Stack Machine youtube mcbride icfp 2012 monday keynote agda-curious

    data Instr = Push Val | Add
    type Val   = Int

    measure needs                :: [Instr] -> Int
    needs (Add    : is)          = min (2, 1 + needs(is))
    needs (Push v : is)          = 0

    run                          :: is:[Instr] -> {v:[Val] | len(v) >= needs(is)} -> [Val]
    run (Add:is)      (x1:x2:vs) = run is (x1 + x2 : vs)
    run (Push v : is) vs         = run is (v : vs)

PROJECT: Termination for Combinator-based Parsers
-------------------------------------------------

btw, did you guys see this:

http://www.reddit.com/r/haskell/comments/1okcmh/odd_space_leak_when_using_parsec/

the poster probably feels silly, but I have, on several occasions, hit
this issue with parsec. Wonder whether our termination checker could be used... hmm...

Sure! You just have to give 

type GenParser tok st = Parsec [tok] st

a size, I guess (len [tok]). The hard part will be to prove it when the size is actually decreasing... 

Hmm... Surely we need to track somehow the "effect" of executing a single parsing action.

For example, 

    chars :: Char -> Parser [Char]
    chars c = do z  <- char c
                 zs <- chars c
                 return (z:zs)

What is the machinery by which the "recursive call" is run on a "smaller" GenParser?
Does it help if we remove the `do` block?

    chars :: Char -> Parser [Char]
    chars c = char c  >>= \z  ->   
              chars c >>= \zs ->
              return (z:zs)

I guess the question becomes, how/where do we specify (let alone verify) that the function
`char c` *consumes* one character, hence causing the `chars` to run on a *smaller* input?


Phew, after banging my head against this all day, this is what I came up with.

You need a measure

   measure eats :: Parser a -> Nat

which describes (a lower bound) on the number of tokens consumed by the action `Parser a`.

Now, you give 

   return :: a -> {v: Parser a | (eats v) = 0}

and most importantly,

   (>>=)  :: forall <Q :: Parser b -> Prop> 
             x: Parser a 
          -> f:{v: a -> Parser b <Q> | (rec v) => (eats x) > 0} 
          -> exists z:Parser b <Q>. {v:Parser b | (eats v) = (eats z) + (eats x)}

(Of course you have to give appropriate signatures for the parsec combinators 
-- perhaps one can even PROVE the `eats` measure. However, note that

   type Parser a = [Char] -> (a, [Char])

roughly speaking, and here `eats` is actually the DIFFERENCE of the lengths of
the input and output [Char] ... so I'm not sure how exactly we would reason about 
the IMPLEMENTATION of `eats` but certainly we should be able to USE it in clients 
of parsec.
 
Note that you need a refinement ON the function type, the idea being that:

1. the BODY of a recursive function is checked in the termination-strengthened
environment that constrains the function to satisfy the predicate `rec`

2. whenever you use >>= on a recursive function, the PRECEDING action must have 
consumed some tokens.

3. the number of tokens consumed by the combined action equals the sum of the two 
actions (all the business about exists z and Q is to allow us to depend on the output
value of `f` (c.f. tests/pos/cont1.hs)


PROJECT: HTT style ST/IO reasoning with Abstract Refinements
------------------------------------------------------------

Can we use abstract refinements to do "stateful reasoning", 
e.g. about stuff in `IO` ? For example, to read files, this 
is the API:

    open  :: FilePath -> IO Handle
    read  :: Handle -> IO String
    write :: Handle -> String -> IO ()
    close :: Handle -> IO ()

The catch is that `read` and `write` require the `Handle` to be 
in an "open" state (which is the state of the `Handle` returned by `open`)
while `close` presumably puts the `Handle` in a "closed" state.

So, suppose we parameterize IO with two predicates a `Pre` and `Post` condition

    data IO a <Pre :: World -> Prop> <Post :: a -> World -> World -> Prop>

where `World` is some abstract type denoting the global machine state.
Now, it should be possible to give types like:

   (>>=)  :: IO a <P, Q> -> (a -> IO b<Q, R>) -> IO b<P, R>
   return :: a -> IO a <P, P>

which basically state whats going on with connecting the conditions, and then,
give types to the File API:

   open  :: FilePath -> IO Handle <\_ -> True> <\h _ w -> (IsOpen h w)>
   read  :: h:Handle -> IO String <\w -> (IsOpen h w)> <\_ _ w -> (IsOpen h w)>
   close :: h:Handle -> IO ()     <\w -> (IsOpen h w)> <\_ _ w -> not (IsOpen h w)>

Wonder if something like this would work?


One of the hardest steps seem to type the monad function (>>=):


So, suppose we parameterize IO with two predicates a `Pre` and `Post` condition

    data IO a <Pre :: World -> Prop> <Post :: a -> World -> World -> Prop>

where `World` is some abstract type denoting the global machine state.
Now, it should be possible to give types like:

   (>>=)  :: IO a <P, Q> -> (a -> IO b<Q, R>) -> IO b<P, R>
   return :: a -> IO a <P, P>



My question is how do you make Q from a post-condition (Q :: a -> Word -> Word -> Prop) 
to a pre-condition.
I guess you need to apply a value x :: a and a w :: Word to write (a -> IO b<Q x w, R>).

I think the problem is that the "correct" values x and w are not "in scope"
 

So assume
data IO a <P :: Word -> Prop, Q: a -> Word -> Word -> Prop> = IO (x:Word<P> -> (y:a, Word<Q y x>))

and you want to type

bind :: IO a <P,Q> -> (a -> IO b <Q x w, R>) -> IO b <P,R>
bind (IO m) k = IO $ \s -> case m s of (a, s') -> (unIO (k a)) s'

You have

IO m :: IO a <P. Q>  
             => m :: xx:Word <P> -> (y:a, Word <Q y xx>)

you can assume
s:: Word <P>

so 
m s :: (y:a, Word <Q y s>)

k a :: IO b <Q x w, R>

uniIO (k a) :: z:Word <Q x w> -> (xx:b, Word <R xx z>)

and we want 
(uniIO k a) s :: (xx:b , Word <R xx s>) 

so basically we need 
P  => Q x w
to be able to make the final application





PROJECT: Using `Dynamic` + Refinements for Mixed Records
--------------------------------------------------------

Haskell has a class (and related functions)

    toDyn   :: (Typeable a) => a -> Dynamic
    fromDyn :: (Typeable a) => Dynamic -> Maybe a

Q: How to encode *heterogenous* maps like:

    d1 = { "name"  : "Ranjit"
         , "age"   : 36
         , "alive" : True
         }

   and also:

    d2 = { "name"    : "Jupiter"
         , "position": 5
         }

   so that you can write generic *duck-typed* functions like

    showName :: Dict -> String

   and write

    showName d1 
    showName d2

   or even

    map showName [d1, d2]

Step 1: Encode dictionary as vanilla Haskell type

    type Dict <Q :: String -> Dynamic -> Prop> = Map String Dynamic <Q>
    empty :: Dict
    put   :: (Dynamic a) => String -> a -> Dict -> Dict
    get   :: (Dynamic a) => String -> Dict -> Dict

Step 2: **Create** dictionaries 

    d1 = put "name"   "RJ"
       $ put "age"    36
       $ put "alive"  True 
       $ empty
       
    d1 = put "name"   "Jupiter"
       $ put "pos"    5 
       $ empty

Step 3: **Lookup** dictionaries

    showName :: Dict -> String
    showName d = get "name" d

    -- TODO: how to support
    showName :: Dict -> Dict 
    incrAge d = put "age" (n + 1) d 
      where 
            n = get "age" d

    -- TODO: how to support
    concat :: Dict -> Dict -> Dict

Step 4: Can directly, without any casting nonsense, call

    showName d1
    showName d2

Need to reflect *Haskell Type* (or at least, `TypeRep` values)
inside logic, so you can write measures like

    measure TypeOf :: a -> Type

and use it to define refinements like 

    (TypeOf v = Int) 

(TODO: too bad we don't have relational measures... or multi-param measures ... yet!)

which we can macro up thus.

    predicate HasType V T = (TypeOf V = T)

    predicate Fld K V N T = (K = N => (HasType V T))

Step 5: Refined Signatures for `Dict` API

    put :: (Dynamic a) => key:String
                       -> {value:a | (Q key value)}
                       -> d:Dict <Q /\ {\k _ -> k /= key}> 
                       -> Dict <Q /\ {\k v -> (Fld k v key a)}>
                       
    get :: (Dynamic a) => key:String
                       -> d:Dict <{\k v -> (Fld k v key a)}> 
                       -> a

Step 6: Now, for example, we should be able to type our dictionaries as

    {-@ d1 :: Dict<Q1> @-}

where 

    Q1 == \k v -> Fld k v "name"  String /\ 
                  Fld k v "age"   Int    /\ 
                  Fld k v "alive" Bool   

and 

    {-@ d2 :: Dict<Q2> @-}

where

    Q2 == \k v -> Fld k v "name"  String /\ 
                  Fld k v "pos"   Int    /\ 

**TODO:**

+ add support for `Type` inside logic
  + needed for `TypeOf` measure, equality checks
  + requires doing type-substitutions inside refinements

+ add support for 
  + update [isn't that just `put`?]
  + concat

+ add support traversals (cf. *Ur*)
  - Fold   (over all fields, eg. to serialize into a String)
  - Map?   (transform all fields to serialize) toDB?
  - Filter (takes a predicate that should only read valid columns of the record)



