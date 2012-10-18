TODO
====

* parse predicate signatures for tuples 
* predicate-aliases 
* Blogging 
* benchmarks: Data.List (foldr)
* predicate-aliases 
* self-invariants        (tests/todo/maybe4.hs)
* fixpoint profile (how much performance hit from -nosimple?)
* Set Theory
* benchmarks: Data.List (foldr) -- needs sets
* benchmarks: Data.Bytestring
* benchmarks: stackset-core
* benchmarks: Data.Text
* benchmarks: mcbrides stack machine
* alpha-renaming of predicate params is VERY SHAKY. see tests/pos/deptupW.hs
* remove `toType` and  generalize `typeSort` to work for all RefTypables


Set Theory
==========

HEREWEARE

(tests/pos/meas9.hs)

1. fixpoint/theories.ml [DONE]
   see fixpoint/tests/sets.fq

2. embed

 Spec   :  ++ EmbedTyCon a = Embed a Fixpoint.Tycon
   
 Parser : parse in the above from specs

 Bare   : EmbedTyCon String -> EmbedTyCon GHC.TyCon

 typeSort : Map GHC.TyCon Fixpoint.Tycon -> Type -> Sort

 Fixpoint: 

    intTC  = "int"
    boolTC = "bool"

 include/Prelude.spec
 
    embed Int       as int
    embed Integer   as int
    embed Bool      as bool
    
 include/Data/Set.spec
    
    embed Set       as Set_Set

------------------------------------------------------------



    measure emp :: Set a 
    measure mem :: a     -> Set a -> Bool
    measure cup :: Set a -> Set a -> Set a
    measure cap :: Set a -> set a -> Set a
    measure elt :: a     -> Set a

    axiom set_emp
      :: x:a
      -> {v: Bool | ~ (mem(x, emp))}

    axiom set_elt
      :: x:a
      -> y:a
      -> {v: Bool | (mem(x, elt(y)) <=> (x = y))}

    axiom set_cup
      :: x:a 
      -> s1: Set a 
      -> s2: Set a 
      -> {v: Bool | (mem(x, cup(s1, s2)) <=> (mem(x, s1) || mem(x, s2)))}

    axiom set_cap
      :: x:a 
      -> s1: Set a 
      -> s2: Set a 
      -> {v: Bool | (mem(x, cup(s1, s2)) <=> (mem(x, s1) && mem(x, s2)))}

    axiom set_eq
      :: s1:Set a
      -> s2:Set a
      -> {v: Bool | seteq(s1, s2) <=> (forall x. (mem(x, s1) <=> mem(x, s2))) }


forall x, S, T: 
  S = T <=> (x in S <=> x in T)

    measure elts :: [a] -> Set a
    elts []      = emp
    elts (x:xs)  = cup (elt(x), elts(xs)) 

   
    prop_set1 



Strictness Annotations  
======================

Seem to screw up measures. See tests/pos/maybe000.hs

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

Fixpoint Profile
================

Where is all the time going in Fixpoint?
    
    liquid ../benchmarks/containers-0.5.0.0/Data/Map/Base.hs

    Solve.acsolve                 280.170 s
      refine                        73.057 s

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

SLICE causes problem in neg/ass0.hs, doesn't really help either so may as well nuke, but find bug in fixpoint 


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

