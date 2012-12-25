TODO
====

* pre-"release" checklist 
    * type-alias: sparseVector <------------------ HEREHEREHEREHERE
    * wierd-annot-for-absoluteSum.go
   
    * web demo: list name of Module not XXXASDADADAd.hs 
    * move demo to liquid/haskell/demo
    * move blog to liquid/haskell/blog
    * direct link to demo for each blog entry

    * DEFAULT "true" spec for all exported top-level functions
    * web demo: error message -- expected XXX got YYY?
    * qualified names break spec imports -- tests/todo/qualifiedvector.hs 

* clean up (Int) -> Int [BEXPARSER]
* parse predicate signatures for tuples 
* benchmarks: stackset-core
* Blogging 
* benchmarks: Data.List (foldr)
* benchmarks: Data.List (foldr) 
* benchmarks: Data.Bytestring
* benchmarks: Data.Text
* benchmarks: mcbrides stack machine
* remove `toType` and  generalize `typeSort` to work for all RefTypables

BExp Parser vs. ppr_rtype [BEXPARSER]
=====================================

WTF is up with the wierd case BEXPARSER?

Why does it kill the BExp parser e.g. tests/pos/LambdaEval.hs (ask Niki)


Type-Alias
==========

How do we allow this?

{-@ type SparseVector a n = [({v: Int | (Btwn 0 v n)}, a)] @-}
{-@ sparseDotProduct :: (Num a) => x:(Vector a) -> (SparseVector a (vlen x)) -> a @-}

- Add an "Expr" form to RType / Bare
    | RExpr Expr    -- only to parse Bare Applications for type aliases with Expr arguments 

- Update parser to handle above

- Update alias-transformer

Benchmarks
==========

                        time(O|N|C)    TOTAL(O|N)   solve (O|N)      refines       iterfreq
    Map.hs          :    54/50/32/10    21/15/8.7      14/8/4.3    9100/4900/2700    16/28/7
    ListSort.hs     :   */7.5/5.5/2    */2.5/1.8     */1.5/1.0      */1100/600       */9/7
    GhcListSort.hs  :    23/22/17/5    7.3/7.8/5   4.5/5.0/2.7    3700/4400/1900   10/23/6
    LambdaEval.hs   :    36/32/25/12    17/12/10     11.7/6.0/5    8500/3100/2400   12/5/5
    Base.hs         :        26mi/2m

Benchmarks
==========

                    time(O|N|C)    TOTAL(O|N)   solve (O|N)      refines       iterfreq
Map.hs          :    54/50/32/10    21/15/8.7      14/8/4.3    9100/4900/2700    16/28/7
ListSort.hs     :   */7.5/5.5/2    */2.5/1.8     */1.5/1.0      */1100/600       */9/7
GhcListSort.hs  :    23/22/17/5    7.3/7.8/5   4.5/5.0/2.7    3700/4400/1900   10/23/6
LambdaEval.hs   :    36/32/25/12    17/12/10     11.7/6.0/5    8500/3100/2400   12/5/5
Base.hs         :        26mi/2m

WebDemo
=======

web/

- tweak so that annothtml doesnt have title -- just BODY

Tuple Refinements (DONE: by Niki)
=================================

- Add/Parse predicate signatures for tuples<p>     

    (x1, x2, x3)<p1, p2, p3>

- pos/deptup.hs (type signature: for constructor wrapper)


    data [a]<p :: a -> a -> Bool> 
      = []
      | (:) (h :: a) (t :: [a<p h>]<p>)  
    
    data (a1, a2) 
      < p1 :: a1 -> Bool
      , p2 :: a1 -> a2 -> Bool
      > 
      = (,) (x1 :: a1<p1>) (x2 :: a2<p2 x1>)
    
    data (a1, a2, a3) 
      < p1 :: a1 -> Bool
      , p2 :: a1 -> a2 -> Bool
      , p3 :: a1 -> a2 -> a3 -> Bool
      > 
      = (,) (x1 :: a1<p1>) (x2 :: a2<p2 x1>) (x3 :: a3<p3 x1 x2>)
    
    data (a1, a2, a3) 
      < p1 :: a1 -> Bool
      , p2 :: a1 -> a2 -> Bool
      , p3 :: a1 -> a2 -> a3 -> Bool
      , p4 :: a1 -> a2 -> a3 -> a4 -> Bool
      > 
      = (,) (x1 :: a1<p1>) (x2 :: a2<p2 x1>) (x3 :: a3<p3 x1 x2>) (x4 :: a4<p4 x1 x2 x3>)

Blog Todo List
==============

- Cleanup output (tests/pos/poly0.hs)

Basic Refinement Types
----------------------

1. RefTypes 101  (Basic Ints, abz, div-by-zero)
2. Dependent Refinements: (Data.Vector, recursion-sum, loop, dotproduct, range, map, fold)

Measures
--------

3. Lists I       (append, reverse, map-length, filter)
4. Lists I-Sets  ("" but with Sets as the measure)
5. Lists II      (take, transpose)
6. MapReduce
7. KMeans        (++ zipWith etc.)
8. LambdaEval

Abstract Refinements
--------------------

9.  (esop) ParaPoly/Ty
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
        > ordering
        > size
        > key-set-properties
        > key-dependence
        > balance (NO)

->   Data.Bytestring & Client 

->   Data.Text (client of bytestring?)
        http://hackage.haskell.org/packages/archive/text/0.11.2.2/doc/html/Data-Text-Lazy-Internal.html
        (See "main invariant")

->   Data.Vector

->   vector-algorithms "vector bounds checking"
     > e.g. "unsafeSlice"
     > maybe only specify types for Vector?

->   xmonad real properties

[??-PP] Xmonad-StackSet-Toy
(zippering-??)

Other Benchmarks
================

->   hmatrix
     > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Matrix.html#Matrix
     > http://hackage.haskell.org/packages/archive/hmatrix/0.12.0.1/doc/html/src/Data-Packed-Internal-Vector.html#fromList
->   FingerTrees (containers / Data.Seq)
->   Union-Find (PLDI09 port if necessary?)
->   BDD        (PLDI09 port if necessary?)
->   Bodik's hairy sparse matrix benchmark?


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

- To make local branch goo

    $ git branch foo
    $ git checkout foo
    $ ...
    $ git commit -a -m "did work in foo"

- To send branch to the mothership

    $ git push origin foo

- To work with branch elsewhere

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

McBride's Stack Machine youtube mcbride icfp 2012 monday keynote agda-curious

    data Instr = Push Val | Add
    type Val   = Int

    measure needs                :: [Instr] -> Int
    needs (Add    : is)          = min (2, 1 + needs(is))
    needs (Push v : is)          = 0

    run                          :: is:[Instr] -> {v:[Val] | len(v) >= needs(is)} -> [Val]
    run (Add:is)      (x1:x2:vs) = run is (x1 + x2 : vs)
    run (Push v : is) vs         = run is (v : vs)

----------------------------------------------------------------------------

NIKITODO

Failed 17 tests: pos/ListISort.hs, pos/ListMSort.hs, pos/ListQSort.hs, pos/ListRange.hs, pos/mapreduce-bare.hs, pos/mapreduce.hs, pos/meas0.hs, pos/meas0a.hs, pos/meas1.hs, pos/meas2.hs, pos/meas3.hs, pos/meas4.hs, pos/meas5.hs, pos/meas6.hs, pos/poly3.hs, pos/poly3a.hs, pos/range.hs



change .html fix (cat fix# leave name)

fix transformations 	*  see list insert for rec
											*  move transformations to initial statgw st anormalized

deptup???
transpose???

------------------------------------------------------

Constrains : split[C|W], unifyS :add c1 == c2 in Class & ConApp

unifyS do I really need to keep track of preds?

	eg neg concat1 -> CB REC trueTy

