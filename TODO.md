TODO
====
    
* performance
    * use -sortedquals switch for fixpoint. why is it NOT used?!
* parse predicate signatures for tuples 
* predicate-aliases 
* Blogging 
* benchmarks: Data.List (foldr)
* self-invariants        (tests/todo/maybe4.hs)
* fixpoint profile (how much performance hit from -nosimple?)

* benchmarks: Data.List (foldr) -- needs sets
* benchmarks: Data.Bytestring
* benchmarks: stackset-core
* benchmarks: Data.Text
* benchmarks: mcbrides stack machine
* remove `toType` and  generalize `typeSort` to work for all RefTypables

Performance
===========

-- NEW BRANCH

- Serializing to .fq is WAY slow 
    - time liquid benchmarks/esop2013-submission/Base.hs > log.base 2>&1
        user	24m21.007s

- What is happening inside fq?  (for Base.hs)

Majority of remaining 900s in haskell land? doing what? serialize/parse?

TOTAL                         530.841 s
  save                           6.204 s
  solve                         237.431 s
    Solve.unsatcs                 40.451 s
    Solve.acsolve                 195.876 s
     Solve.acsolve                 195.876 s
      refine                        103.502 s
  Validate                      71.492 s
    valid rhs                      1.864 s
      validate_vars                  0.404 s
      preds_of_reft                  1.068 s
    validate_vars                  4.544 s
  Qual Inst                     195.672 s

- Where is all the time going in Fixpoint?
    - Why so many iterations? Why are ANY constraints seen more than 1 (or maybe 2) times?

        ---> STRIPPED lambdaTiny even more so below dont apply.


        liquid tests/pos/LambdaEvalTiny.hs
        time ./external/fixpoint/fixpoint.native -notruekvars -refinesort  -strictsortcheck external/fixpoint/LambdaEvalTiny.hs.fq
        
        ITERFREQ: 1 times (ch = false) 20 constraints 229,81,235,11,12,163,173,253,255,183,114,39,265,203,53,210,289,67,143,223 
        ITERFREQ: 1 times (ch = true) 50 constraints 27,179,254,183,33,259,114,189,190,265,266,267,268,271,122,47,124,126,127,277,203,128,278,129,209,61,62,213,149,75,150,1,229,4,230,231,232,10,163,13,89,91,241,16,243,169,244,247,22,173 
        ITERFREQ: 2 times (ch = false) 8 constraints 160,242,94,106,256,200,219,220 
        ITERFREQ: 2 times (ch = true) 8 constraints 180,191,200,130,210,151,160,170 
        ITERFREQ: 3 times (ch = false) 4 constraints 180,190,191,209 
        ITERFREQ: 4 times (ch = false) 5 constraints 169,170,179,189,149 
        ITERFREQ: 5 times (ch = false) 1 constraints 151 
        ITERFREQ: 7 times (ch = false) 2 constraints 150,130 
        ITERFREQ: 8 times (ch = false) 5 constraints 75,89,129,139,140 
        ITERFREQ: 9 times (ch = false) 19 constraints 77,78,87,88,90,91,100,101,102,103,47,126,127,128,62,63,64,73,74 
        ITERFREQ: 10 times (ch = false) 8 constraints 36,45,46,49,50,59,60,61 
        ITERFREQ: 11 times (ch = false) 1 constraints 35 


         77  rhs {VV : Tuple ([Tuple int   Expr])   Expr | [k_206]}
        ,78  rhs {VV : [Tuple int   Expr] | [k_203]}
        ,87  rhs {VV : Expr | [k_204]}
        ,88  rhs {VV : Expr | [k_205[fld:=fld]]}

        ,90  rhs {VV : Tuple ([Tuple int   Expr])   Expr | [k_45[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        ,91  rhs {VV : [Tuple int   Expr] | [k_42[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        ,100 rhs {VV : Expr | [k_43[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        
        ,101 rhs {VV : Expr | [k_44[ds_djf:=ds_djf][fld:=fld][sto#aiB:=sto#aiB]]}
        ,102 rhs {VV : Expr | [k_33[sto#aiB:=lq_anf__djw]]}
        ,103 rhs {VV : [Tuple int   Expr] | [k_32]}
        ,47  rhs {VV : State# RealWorld | [k_222]}
        ,126 rhs {VV : Expr | [k_180]}
        ,127 rhs {VV : int | [k_179]}
        ,128 rhs {VV : Expr | [k_168]}
        
        ,62  rhs {VV : Expr | [k_219]}
        ,63  rhs {VV : Tuple ([Tuple int   Expr])   Expr | [k_45[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        ,64  rhs {VV : [Tuple int   Expr] | [k_42[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        ,73  rhs {VV : Expr | [k_43[ds_djf:=ds_djf][sto#aiB:=sto#aiB]]}
        ,74  rhs {VV : Expr | [k_44[ds_djf:=ds_djf][fld:=fld][sto#aiB:=sto#aiB]]}

    90 >> 90
    90 >> 102 >> 90
    90 >> 35 >> 90 >> ??
    ?? >> 139 >> 90

Heres a random cycle!

    90 >> 46 >> 129 >> 128 >> 90



  90 -> 35; -- 11
  90 -> 36; -- 10
  90 -> 39; -- 1
  90 -> 45; -- 10
  90 -> 46; -- 10 
  90 -> 47; -- 9
  90 -> 49;
  90 -> 50;
  90 -> 53; -- 1
  90 -> 59;
  90 -> 60;
  90 -> 61;
  90 -> 62;
  90 -> 63;
  90 -> 64;
  90 -> 67; -- 1
  90 -> 73;
  90 -> 74;
  90 -> 75;
  90 -> 77;
  90 -> 78;
  90 -> 81; -- 1
  90 -> 87;
  90 -> 88;
  90 -> 89;
  90 -> 90;
  90 -> 91;
  90 -> 94;
  90 -> 100;
  90 -> 101;
  90 -> 102;
  90 -> 103;
  90 -> 106;
  90 -> 114;
  90 -> 122;
  90 -> 124;
  90 -> 126;
  90 -> 127;
  90 -> 128;
  90 -> 129;
  90 -> 130;
  90 -> 139;
  90 -> 140;
  90 -> 143;
  90 -> 149;
  90 -> 150;
  90 -> 151;
  90 -> 160;
  90 -> 163;
  90 -> 169;
  90 -> 170;
  90 -> 173;
  90 -> 179;
  90 -> 180;
  90 -> 183;
  90 -> 189;
  90 -> 190;
  90 -> 191;
  90 -> 200;
  90 -> 203;
  90 -> 209;
  90 -> 210;
  90 -> 213;
 
real	0m44.740s
user	0m36.330s
Fixpoint Solver Time 
TOTAL                         18.885 s
  solve                         12.837 s
    Solve.unsatcs                  1.516 s



    liquid ../benchmarks/containers-0.5.0.0/Data/Map/Base.hs

    Solve.acsolve                 280.170 s
      refine                        73.057 s

liquid benchmarks/esop2013/Base.hs (goto) -- most time = rendering constraints to .fq!

Fixpoint

TOTAL                         520.290 s
  save                           6.580 s
  solve                         235.400 s
    Solve.unsatcs                 41.700 s
      z3Pred                        30.760 s
    Solve.acsolve                 192.710 s
      refine                        101.170 s
  Validate                      62.380 s
    valid rhs                      1.550 s
      validate_vars                  0.220 s
      preds_of_reft                  1.140 s
    validate_vars                  3.370 s
  parse                         16.720 s
  Qual Inst                     197.370 s


Self-Invariants
===============

Hack binders to allow things like this:

    invariant z:{v: Maybe {isJust(v) && (v = fromJust(z))}} 

Currently hacked by "copying variables", 

see tests/pos/maybe3.hs [hack which works]
    tests/pos/maybe4.hs [deal with devil which doesn't work]

Predicate Aliases
=================

Then clean up the spec blowup in containers/Data/Map/Base.hs ?

    {-@ maybeGe(lo, v)     = ((isJustS(lo)) => (v >= fromJustS(lo))) @-}
    {-@ maybeLe(hi, v)     = ((isJustS(lo)) => (v <= fromJustS(hi))) @-}
    {-@ inRange(lo, hi, v) = maybeGe(lo, v) && maybeLe(hi, v)        @-}

Instead of the grisly

    inRange(lo, hi, v) = {v:k | (((isJustS(lo)) => (v >= fromJustS(lo))) && (((isJustS(hi)) => (v <= fromJustS(hi)))))} v @-}

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


Blogging 
========

    0. *** Cleanup output (tests/pos/poly0.hs)
    1.  Trivial Stuff (incr, pos, map, fold, etc.)
    2.  Lists I       (append, reverse, map-length, filter)
    3.  Lists II      (take, transpose)
    4.  Lists III     (induction with fold) 
    5.  KMeans        (++ zipWith etc.)
    6.  LambdaEval
    7.  Sorting I     (Insert)
    8.  Sorting II    (Merge, Quick, GHC-wierd-sort)
    9.  Map  I        (BST property, add, delete)
    10. Map II        (Data.Map with elements etc.)
    11. Binary Tree/ Finger Tree?
    12. BDD
    13. Union Find
    14. XMonad I
    15. XMonad II

Paper #2 (Liquid Types in the Real World)
=========================================

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

->   vector/

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

