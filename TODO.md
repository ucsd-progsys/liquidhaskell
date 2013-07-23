TODO
====

* incremental checking (see below) 
    - save top-level types to file (.spec)
    - reload
    - check all but specified function

* Qualified Imports
  - wtf is include/KMeansHelper.hs ? Fix module import issue
  - break spec imports -- tests/todo/qualifiedvector.hs 

* benchmarks: Data.Bytestring
    ? readsPrec
    ? big constants issue : _word64 34534523452134213524525 due to (deriving Typeable)

* error messages
  + expected XXX got YYY?
  + liquid-fixpoint sort checker return ERROR (not than errorstar-inside) for nicer messages.

* benchmarks
  + stackset-core
  + Data.List (foldr)
  + mcbrides stack machined?

Incremental Checking
--------------------

    Language.Haskell.Liquid.IncCheck

+ finish implementation of missing code
+ In `Liquid.hs` add code to SAVE the old file
+ 


Liquid-Fixpoint SMTLIB2
-----------------------

SETS-RELATED

  ../web/demos/ListElts.hs,
  ../web/demos/TalkingAboutSets.hs,
  ../web/demos/refinements101reax.hs,
  ../web/demos/UniqueZipper.hs,
  pos/ListConcat.hs,
  pos/ListElem.hs,
  pos/SS.hs,
  pos/cont.hs,
  pos/deepmeas0.hs,
  pos/listSet.hs,
  pos/listSetDemo.hs,
  pos/meas10.hs,
  pos/meas11.hs,
  pos/meas9.hs,
  pos/stacks0.hs,
  pos/zipper.hs,
  pos/zipper0.hs 

MATHSAT [no support for mod?]

Terminated
1364.656211 seconds
FAILURE :( (../benchmarks/esop2013-submission/Splay.hs) 

1381.994545 seconds
FAILURE :( (../web/demos/Array.hs) 

1383.221166 seconds
FAILURE :( (../benchmarks/esop2013-submission/Base.hs) 

Exceptions thrown on 11 tests: 
  ../benchmarks/esop2013-submission/Array.hs,
  ../benchmarks/esop2013-submission/Base.hs,
  ../benchmarks/esop2013-submission/Splay.hs,
  ../benchmarks/esop2013-submission/Toy.hs,
  ../web/demos/Array.hs,
  ../web/demos/Loop.hs,
  ../web/demos/SimpleRefinements.hs,
  ../web/demos/absref101.hs,
  ../web/demos/refinements101.hs,
  pos/initarray.hs,
  pos/modTest.hs 



Embed
-----

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


Module Import (branch: imports) 
-------------------------------

See tests/pos/Mod2.hs [Which imports a measure from Mod1.hs]

    [STOP] Get tests to run WITHOUT after deleting *redundant*

    import qualified Mod1

0. NO MONOLITHIC "bare".
 
   >   When converting a SPEC, do so in its own context.

1. When Parsing IMPORTED module, FULL QUALIFY all names 

    a. write specs WITHOUT QUALIFICATION
    b. Remember MODULE name when parsing spec
    c. reJigger so DataCon/TyCon/Id get slapped with the module name (if not qualified)

2. When Parsing TARGET module, REMEMBER all qualifications 

        [Foo.Bar.Baz as F, ...]

3. When GHC-Lookup-ing, use above table:

    name of DataCon/TyCon/Id in file

        x

    name after FULL expansion (1)

        Foo.Bar.Baz.x

    name after qualification
        
        F.x

    use F.x when doing GHC-lookup.


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
?. LambdaEval	

Abstract Refinements
--------------------

[DONE]  (esop) ParaPoly/Ty  <--------------- STOP 
10. (esop) Pats Vec
11. Niki DataBase
12. Induction-Loop
13. Induction-List (efoldr)

Abstract Refinements (Rec)
--------------------------

14. Sorting I     (Insert)
15. Sorting II    (Merge, Quick) 
16. Sorting III   (GHC-quick) 
17. Sorting IV    (GHC-merge)
18. Sorting V     (GHC-real)
19. Map  I        (BST property, add, delete)
20. Map II        (Data.Map with elements etc.)

Future Work
-----------

- StackSet      ...
- Binary Tree/ Finger Tree?
- BDD
- Union Find
- XMonad I
- XMonad II

Paper: Liquid Types in the Real World)
======================================

[OK]    Data.KMeans

[OK]    GHC.List   (../benchmarks/ghc-7.4.1/List.lhs)

[??-PP] Data.Map (supersedes set)
        > ordering [OK]
        > size
        > key-set-properties
        > key-dependence
        > balance (NO)
        
->   	Xmonad real properties

->   	Data.Vector

->   	vector-algorithms "vector bounds checking"
     	> e.g. "unsafeSlice"
     	> maybe only specify types for Vector?

Other Benchmarks
================

->   hmatrix
     > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Matrix.html#Matrix
     > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Vector.html#fromList
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

Alpha-Renaming Predicates
=========================

see tests/pos/deptupW.hs

We SHOULD be able to write 

    {-@ data Pair a b <p :: x0:a -> x1:b -> Bool> = P (x :: a) (y :: b<p x>) @-} 
    data Pair a b = P a b

and then write the function sig like:

    {-@ mkP :: forall a <p :: y0:a -> y1:a -> Bool>. x: a -> y: a<p x> -> Pair <p> a a @-}
    
instead of HAVING TO use the SAME parameter names x0, x1



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

