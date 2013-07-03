TODO
====


* Qualified Import Issue: wtf is include/KMeansHelper.hs ? Fix module import issue

* [jhala]  benchmarks: Data.Bytestring
    ? readsPrec
    ? big constants issue : _word64 34534523452134213524525 due to (deriving Typeable)

* error messages: expected XXX got YYY?

* incremental checking (see below) 
    - save top-level types to file (.spec)
    - reload
    - check all but specified function

* have liquid-fixpoint sort checker RETURN ERROR (rather than errorstar-inside) so we can give nicer messages.


* qualified names break spec imports -- tests/todo/qualifiedvector.hs 

* DEFAULT "true" spec for all exported top-level functions (tests/neg/truespec.hs)
  -> may break a LOT of regressions

* [seidel] benchmarks: Data.Text
* benchmarks: stackset-core
* benchmarks: Data.List (foldr)
* benchmarks: Data.List (foldr) 
* benchmarks: mcbrides stack machine
* Move stuff into Types.hs
    - remove `toType` and  generalize `typeSort` to work for all RefTypables

Bytestring
==========

Ordered by dependency.

   148 Data/ByteString/Lazy/Internal.hs     [OK]
   297 Data/ByteString/Unsafe.hs            [OK+T]
   509 Data/ByteString/Internal.hs          [OK+T]
   700 Data/ByteString/Fusion{T}.hs         [OK]
  1928 Data/ByteString.hs                   [OK]
  
  1322 Data/ByteString/Lazy.hs               
   822 Data/ByteString/Lazy/Char8.hs
  1012 Data/ByteString/Char8.hs

  6738 total





Text
====

   387 ./Data/Text/Fusion.hs
   427 ./Data/Text/Encoding.hs
   225 ./Data/Text/Read.hs
   124 ./Data/Text/Fusion/Internal.hs
   181 ./Data/Text/Fusion/Size.hs
   908 ./Data/Text/Fusion/Common.hs
   456 ./Data/Text/Fusion/CaseMapping.hs
   334 ./Data/Text/IO.hs
   216 ./Data/Text/Internal.hs
    42 ./Data/Text/Axioms.hs
   205 ./Data/Text/Encoding/Fusion.hs
    23 ./Data/Text/Encoding/Utf32.hs
   147 ./Data/Text/Encoding/Fusion/Common.hs
    42 ./Data/Text/Encoding/Utf16.hs
   161 ./Data/Text/Encoding/Utf8.hs
   116 ./Data/Text/Encoding/Error.hs
   185 ./Data/Text/Unsafe.hs
   116 ./Data/Text/UnsafeChar.hs
   454 ./Data/Text/Array.hs
    69 ./Data/Text/UnsafeShift.hs
   215 ./Data/Text/Foreign.hs
    29 ./Data/Text/Util.hs
   375 ./Data/Text/Encoding.small.hs
   116 ./Data/Text/Lazy.small.hs
   170 ./Data/Text/Search.hs
   166 ./Data/Text/IO/Internal.hs
  1930 ./Data/Text/Lazy.hs
   144 ./Data/Text/Lazy/Fusion.hs
   270 ./Data/Text/Lazy/Encoding.hs
   215 ./Data/Text/Lazy/Read.hs
   207 ./Data/Text/Lazy/IO.hs
   192 ./Data/Text/Lazy/Internal.hs
   321 ./Data/Text/Lazy/Encoding/Fusion.hs
   239 ./Data/Text/Lazy/Builder/RealFloat.hs
   190 ./Data/Text/Lazy/Builder/Int.hs
    25 ./Data/Text/Lazy/Builder/RealFloat/Functions.hs
    35 ./Data/Text/Lazy/Builder/Functions.hs
   342 ./Data/Text/Lazy/Search.hs
   387 ./Data/Text/Lazy/Builder.hs
    50 ./Data/Text/Private.hs
    55 ./Data/Text/Unsafe/Base.hs
  2038 ./Data/Text.hs
   139 ./Data/Text.small.hs
 12668 total


****************************** WARNING: Data/ByteString.split.0.hs:267:51 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:317:20-22 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:331:20-22 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:342:20-22 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:463:19-21 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:829:45-46 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:853:55-57 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:980:44-46 *****************************
****************************** WARNING: Data/ByteString.split.0.hs:1076:60-62 *****************************

CANNOT PROVE TERMINATION EVER!

{-@ unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString @-}
unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f = concat . unfoldChunk 32 64
  where unfoldChunk n n' x =
          case unfoldrN n f x of
            (s, Nothing) -> s : []
            (s, Just x') -> s : unfoldChunk n' (n+n') x'

Liquid-Fixpoint
===============

Z3 agnostic solver? sigh.

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


Module Import (see branch imports) 
==================================

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


Incremental Checking
====================

[see branch "inccheck" look for the field "binds" in CmdLine.hs]

1. Command Line Arguments  
    - Specify WHICH binders to verify [DEFAULT = ALL]  
    - liquid tests/pos/goo.hs -check foo bar baz 
    - Print out vars/hs-types <---------------------- STOPSTOPSTOPSTOPSTOP 

2. CONSGEN for subset 
3. CONSGEN for subset using TRUE for all other functions
4. SAVE out inferred-types for top-level binders
5. REUSE pre-inferred types for other functions 


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
        
->   	Data.Bytestring (& Client?)

->   	Data.Text (client of bytestring?)
        http://hackage.haskell.org/packages/archive/text/0.11.2.2/doc/html/Data-Text-Lazy-Internal.html
        (See "main invariant")

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


change .html fix (cat fix# leave name)

fix transformations 	*  see list insert for rec
											*  move transformations to initial statgw st anormalized

deptup???
transpose???

------------------------------------------------------

Constrains : split[C|W], unifyS :add c1 == c2 in Class & ConApp

unifyS do I really need to keep track of preds?

	eg neg concat1 -> CB REC trueTy
    17,  8.813, num refines=1600>
                        <    18, 15.013, num refines=1700>
                        <    19, 19.189, num refines=1800>
                        <    20, 14.845, num refines=1900>
                        <    21, 10.025, num refines=2000>
                        <    22, 13.773, num refines=2100>
                        <    23, 23.021, num refines=2200>
                        <    24, 10.041, num refines=2300>
                        <    25,  8.213, num refines=2400>
                        <    26,  9.045, num refines=2500>
                        <    27, 12.585, num refines=2600>
                        <    28,  8.949, num refines=2700>
                        <    29,  7.012, num refines=2800>
                        <    30,  9.369, num refines=2900>
                        <    31,  2.512, num refines=3000>
                        <    32,  9.589, num refines=3100>
                        <    33, 15.001, num refines=3200>
                        <    34, 22.013, num refines=3300>
                        <    35, 18.129, Finished>
                         
 
 
# Vars: (Total=2068, False=307) Quals: (Total=13642, Avg=6.596712, Max=185, Min=1)
#Iteration Profile = (si=0 tp=1801 unsatLHS=641 emptyRHS=267) 
#Queries: umatch=281900, match=12941, ask=641913, valid=11250
TP stats: sets=1929, pushes=644502, pops=644502, unsats=11381, queries=642661, count=2661, unsatLHS=0 
 
Fixpoint: Testing Solution 
Unsatisfied Constraints:
 constraint:
 env  [ x0#a3sk:{VV#1970 : a_ts | [k_1971]}
      ; x#a3st:{VV#1992 : a_ts | [k_1993]}
      ; w#a3sv:{VV#1958 : int | [k_1959[x:=ds_d3JK][lq_tmp_x1955:=x#a3st][b:=fix#x#39##35#a3sw][a:=w#a3sv][VV#1967:=lq_anf__d3Ni][VV#1965:=lq_anf__d3Nm]]}
      ; ttrd:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(2)]) | []}
      ; tsnd:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(1)]) | []}
      ; tfst:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(0)]) | []}
      ; sumLens:{VV : func(1, [List (List @(0)) ; int]) | []}
      ; snd:{VV : func(2, [fix##40##41# @(0) @(1) ; @(1)]) | []}
      ; psnd:{VV : func(2, [Data.ByteString.Fusion.PairS @(0) @(1) ; @(1)]) | []}
      ; plen:{VV : func(1, [GHC.Ptr.Ptr @(0) ; int]) | []}
      ; pfst:{VV : func(2, [Data.ByteString.Fusion.PairS @(0) @(1) ; @(0)]) | []}
      ; pbase:{VV : func(1, [GHC.Ptr.Ptr @(0) ; int]) | []}
      ; papp2:{VV : func(4, [Pred @(0) @(1) ; @(2) ; @(3) ; bool]) | []}
      ; papp1:{VV : func(2, [Pred @(0) ; @(1) ; bool]) | []}
      ; p#a3ss:{VV#1990 : GHC.Ptr.Ptr int | [k_1991]}
      ; null:{VV : func(1, [List @(0) ; bool]) | []}
      ; n#a3su:{VV#1994 : int | [k_1995]}
      ; lq_anf__d3Nv:{VV#2120 : int | [(VV#2120 = (n#a3su + lq_anf__d3Nu))]}
      ; lq_anf__d3Nu:{VV#2119 : int | [(VV#2119 = (1 : int))]}
      ; lq_anf__d3Nt:{VV#2118 : GHC.Ptr.Ptr int | [(0 <= plen([VV#2118]))
                                                  ; && [ (pbase([VV#2118]) = pbase([p#a3ss]))
                                                       ; (plen([VV#2118]) = (plen([p#a3ss]) - lq_anf__d3Ns))]]}
      ; lq_anf__d3Ns:{VV#2113 : int | [(VV#2113 = (1 : int))]}
      ; lq_anf__d3Nr:{VV#2112 : int | [(VV#2112 = (ds_d3JQ - lq_anf__d3Nq))]}
      ; lq_anf__d3Nq:{VV#2111 : int | [(VV#2111 = (1 : int))]}
      ; lq_anf__d3Np:{VV#2110 : GHC.Types.IO fix##40##41# | []}
      ; lq_anf__d3No:{VV#2080 : GHC.Types.Bool | [(Prop(VV#2080) <=> (n#a3su = i#a3si))
                                                 ; (VV#2080 = lq_anf__d3Nn)
                                                 ; (~ (Prop(VV#2080)))
                                                 ; (~ (Prop(VV#2080)))]}
      ; lq_anf__d3Nn:{VV#2080 : GHC.Types.Bool | [(Prop(VV#2080) <=> (n#a3su = i#a3si))]}
      ; lq_anf__d3Nm:{VV#1965 : fix##40##41# int a_ts | [k_1966[x:=ds_d3JK][lq_tmp_x1955:=x#a3st][VV#1967:=lq_anf__d3Ni]
                                                        ; (VV#1965 = ds_d3JK)
                                                        ; (VV#1965 = fix#GHC.Tuple.#40##44##41##35#74([w#a3sv; fix#x#39##35#a3sw]))
                                                        ; (snd([VV#1965]) = fix#x#39##35#a3sw)
                                                        ; (fst([VV#1965]) = w#a3sv)]}
      ; lq_anf__d3Ni:{VV#1967 : Data.Maybe.Maybe (fix##40##41# int a_ts) | 
                     [k_1968[lq_tmp_x1955:=x#a3st]; (VV#1967 = lq_anf__d3Nh)
                     ; (VV#1967 = Data.Maybe.Just#r1a([ds_d3JK]))
                     ; (fromJust([VV#1967]) = ds_d3JK)
                     ; (isJust(VV#1967) <=> true)]}
      ; lq_anf__d3Nh:{VV#1967 : Data.Maybe.Maybe (fix##40##41# int a_ts) | 
                     [k_1968[lq_tmp_x1955:=x#a3st]]}
      ; len:{VV : func(1, [List @(0) ; int]) | []}
      ; lbLengths:{VV : func(0, [List Data.ByteString.Lazy.Internal.ByteString ; int]) | []}
      ; lbLength:{VV : func(0, [Data.ByteString.Lazy.Internal.ByteString ; int]) | []}
      ; isNullPtr:{VV : func(1, [GHC.Ptr.Ptr @(0) ; bool]) | []}
      ; isJustS:{VV : func(1, [Data.ByteString.Fusion.MaybeS @(0) ; bool]) | []}
      ; isJust:{VV : func(1, [Data.Maybe.Maybe @(0) ; bool]) | []}
      ; i#a3si:{VV#1952 : int | [k_1953]}
      ; go_unfoldrN#a3C6:{VV : func(0, [int ; GHC.Ptr.Ptr int ; a_ts ; int ; GHC.Types.IO (fix##40##41# int int (Data.Maybe.Maybe a_ts))]) | []}
      ; fst:{VV : func(2, [fix##40##41# @(0) @(1) ; @(0)]) | []}
      ; fromJust:{VV : func(1, [Data.Maybe.Maybe @(0) ; @(0)]) | []}
      ; fplen:{VV : func(1, [GHC.ForeignPtr.ForeignPtr @(0) ; int]) | []}
      ; fix#x#39##35#a3sw:{VV#1960 : a_ts | [k_1961[x:=ds_d3JK][lq_tmp_x1955:=x#a3st][b:=fix#x#39##35#a3sw][a:=w#a3sv][VV#1967:=lq_anf__d3Ni][VV#1965:=lq_anf__d3Nm]
                                            ; k_1964[x:=ds_d3JK][lq_tmp_x1962:=w#a3sv][lq_tmp_x1955:=x#a3st][b:=fix#x#39##35#a3sw][a:=w#a3sv][VV#1967:=lq_anf__d3Ni][VV#1963:=VV#1960]]}
      ; fix#GHC.Types.#91##93##35#6m:{VV : func(1, [List @(0)]) | []}
      ; fix#GHC.Types.#58##35#64:{VV : func(1, [@(0) ; List @(0) ; List @(0)]) | []}
      ; fix#GHC.Tuple.#40##44##44##41##35#76:{VV : func(3, [@(0) ; @(1) ; @(2) ; fix##40##41# @(0) @(1) @(2)]) | []}
      ; fix#GHC.Tuple.#40##44##41##35#74:{VV : func(2, [@(0) ; @(1) ; fix##40##41# @(0) @(1)]) | []}
      ; fix#GHC.Tuple.#40##41##35#70:{VV : fix##40##41# | []}
      ; fix#GHC.Prim.#43##35##35#98:{VV : func(0, [int ; int ; int]) | []}
      ; fix#GHC.Prim.#40##35##44##35##41##35#84:{VV : func(2, [@(0) ; @(1) ; fix##40##41# @(0) @(1)]) | []}
      ; fix#GHC.Classes.D#58#Ord#35#rZT:{VV : func(1, [GHC.Classes.Eq @(0) ; func(0, [@(0) ; @(0) ; GHC.Types.Ordering]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; @(0)]) ; func(0, [@(0) ; @(0) ; @(0)]) ; GHC.Classes.Ord @(0)]) | []}
      ; fix#GHC.Classes.D#58#Eq#35#r11x:{VV : func(1, [func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; GHC.Classes.Eq @(0)]) | []}
      ; fix#GHC.Classes.#38##38##35#r1e:{VV : func(0, [GHC.Types.Bool ; GHC.Types.Bool ; GHC.Types.Bool]) | []}
      ; fix#Data.ByteString.foldr1#39##35#r2WQ:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; fix#Data.ByteString.foldl1#39##35#r2WO:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; fix#Data.ByteString.Lazy.Internal.#36#WChunk#35#r28N:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString]) | []}
      ; fix#Data.ByteString.Internal.#36#WPS#35#r1Pa:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; fix##36##36##39##58##39#:{VV : GHC.Prim.Char# | []}
      ; fix##36##36##39##32##39#:{VV : GHC.Prim.Char# | []}
      ; fix##36##36##34#tail#34#:{VV : int | []}
      ; fix##36##36##34#minimum#34#:{VV : int | []}
      ; fix##36##36##34#maximum#34#:{VV : int | []}
      ; fix##36##36##34#last#34#:{VV : int | []}
      ; fix##36##36##34#init#34#:{VV : int | []}
      ; fix##36##36##34#head#34#:{VV : int | []}
      ; fix##36##36##34#foldr1#34#:{VV : int | []}
      ; fix##36##36##34#foldl1#39##34#:{VV : int | []}
      ; fix##36##36##34#foldl1#34#:{VV : int | []}
      ; fix##36##36##34#empty#32#ByteString#34#:{VV : int | []}
      ; fix##36##36##34#LIQUIDCOMPAT#34#:{VV : int | []}
      ; fix##36##36##34#Data.ByteString.#34#:{VV : int | []}
      ; fix##36##36##34#Data#47#ByteString.split.0.T.hs#58#358#58#21#45#26#34#:
        {VV : int | []}
      ; fix##36##36##34#Data#47#ByteString.split.0.T.hs#58#351#58#19#45#24#34#:
        {VV : int | []}
      ; f#a3sj:{VV : func(0, [a_ts ; Data.Maybe.Maybe (fix##40##41# int a_ts)]) | []}
      ; eta_B3:{VV#1949 : int | [(VV#1949 >= 0)]}
      ; eta_B2:{VV : func(0, [a_ts ; Data.Maybe.Maybe (fix##40##41# int a_ts)]) | []}
      ; eta_B1:{VV : a_ts | []}
      ; ds_d3JQ:{VV#1986 : int | [k_1987]}
      ; ds_d3JN:{VV#2086 : GHC.Prim.State# GHC.Prim.RealWorld | [k_2087]}
      ; ds_d3JK:{VV#1965 : fix##40##41# int a_ts | [k_1966[x:=ds_d3JK][lq_tmp_x1955:=x#a3st][VV#1967:=lq_anf__d3Ni]]}
      ; deref:{VV : func(1, [GHC.Ptr.Ptr @(0) ; @(0)]) | []}
      ; cmp:{VV : func(0, [GHC.Types.Ordering ; GHC.Types.Ordering]) | []}
      ; cStringLen:{VV : func(0, [fix##40##41# (GHC.Ptr.Ptr Foreign.C.Types.CChar) int ; int]) | []}
      ; bPayload:{VV : func(0, [Data.ByteString.Internal.ByteString ; GHC.ForeignPtr.ForeignPtr int]) | []}
      ; bOffset:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; bLengths:{VV : func(0, [List Data.ByteString.Internal.ByteString ; int]) | []}
      ; bLength:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; addrLen:{VV : func(0, [int ; int]) | []}
      ; Set_sub:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; bool]) | []}
      ; Set_sng:{VV : func(1, [@(0) ; Set_Set @(0)]) | []}
      ; Set_mem:{VV : func(1, [@(0) ; Set_Set @(0) ; bool]) | []}
      ; Set_emp:{VV : func(1, [Set_Set @(0) ; bool]) | []}
      ; Set_dif:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Set_cup:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Set_cap:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Prop:{VV : func(0, [GHC.Types.Bool ; bool]) | []}
      ; GHC.Word.W8##r1dO:{VV : func(0, [GHC.Prim.Word# ; int]) | []}
      ; GHC.Types.True#6u:{VV : GHC.Types.Bool | []}
      ; GHC.Types.LT#6S:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.I##6c:{VV : func(0, [int ; int]) | []}
      ; GHC.Types.GT#6W:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.False#68:{VV : GHC.Types.Bool | []}
      ; GHC.Types.EQ#6U:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.C##62:{VV : func(0, [GHC.Prim.Char# ; GHC.Types.Char]) | []}
      ; GHC.Ptr.Ptr#rO5:{VV : func(1, [int ; GHC.Ptr.Ptr @(0)]) | []}
      ; GHC.Prim.realWorld##0f:{VV#356 : GHC.Prim.State# GHC.Prim.RealWorld | []}
      ; GHC.Classes.not#r1d:{VV : func(0, [GHC.Types.Bool ; GHC.Types.Bool]) | []}
      ; GHC.CString.unpackCString##0k:{VV : func(0, [int ; List GHC.Types.Char]) | []}
      ; Data.Maybe.Nothing#r19:{VV : func(1, [Data.Maybe.Maybe @(0)]) | []}
      ; Data.Maybe.Just#r1a:{VV : func(1, [@(0) ; Data.Maybe.Maybe @(0)]) | []}
      ; Data.ByteString.unpackList#r2Ws:{VV : func(0, [Data.ByteString.Internal.ByteString ; List int]) | []}
      ; Data.ByteString.unpack#r2Wp:{VV : func(0, [Data.ByteString.Internal.ByteString ; List int]) | []}
      ; Data.ByteString.uncons#r2Wz:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.Maybe.Maybe (fix##40##41# int Data.ByteString.Internal.ByteString)]) | []}
      ; Data.ByteString.transpose#r2WG:{VV : func(0, [List Data.ByteString.Internal.ByteString ; List Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.takeWhile#r2Xb:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.take#r2X8:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.tail#r2Wy:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.splitAt#r2Xa:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.spanEnd#r2Xi:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.spanByte#r2Xh:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.span#r2Xg:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.sort#r2Xk:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.snoc#r2Ww:{VV : func(0, [Data.ByteString.Internal.ByteString ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.singleton#r2Wn:{VV : func(0, [int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanr1#r2X3:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanr#r2X2:{VV : func(0, [func(0, [int ; int ; int]) ; int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanl1#r2X1:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanl#r2X0:{VV : func(0, [func(0, [int ; int ; int]) ; int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.reverse#r2WE:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.replicate#r2X4:{VV : func(0, [int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.pack#r2Wo:{VV : func(0, [List int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.null#r2Wt:{VV : func(0, [Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.minimum#r2WW:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.maximum#r2WV:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.mapIndexed#r2WZ:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.map#r2WD:{VV : func(0, [func(0, [int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.lengths#r2Wg:{VV : func(0, [List Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.length#r2Wu:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.last#r2WA:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.intersperse#r2WF:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.intercalateWithByte#r2Xj:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.init#r2WB:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.head#r2Wx:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.foldr1#r2WP:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.foldl1#r2WN:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.findIndexOrEnd#r2Xl:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.findFromEndUntil#r2Xp:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.eq#r2Wk:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.empty#r2Wm:{VV#290 : Data.ByteString.Internal.ByteString | 
                                   [true; (bLength([VV#290]) = 0)
                                   ; (0 <= bLength([VV#290]))]}
      ; Data.ByteString.elemIndex#r2Wj:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.Maybe.Maybe int]) | []}
      ; Data.ByteString.dummyForQuals2_splitWith#r2Wi:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.dummyForQuals1_elemIndex#r2Wh:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO (GHC.Ptr.Ptr int)]) | []}
      ; Data.ByteString.dropWhile#r2Xc:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.drop#r2X9:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.cons#r2Wv:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.concatMap#r2WS:{VV : func(0, [func(0, [int ; Data.ByteString.Internal.ByteString]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.concat#r2WR:{VV : func(0, [List Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.breakEnd#r2Xf:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.breakByte#r2Xe:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.break#r2Xd:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.append#r2WC:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.any#r2WT:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.all#r2WU:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.Unsafe.unsafeTake#r1ZE:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Unsafe.unsafeTail#r1ZC:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Unsafe.unsafeHead#r1ZB:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.Unsafe.unsafeDrop#r1ZF:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Lazy.Internal.Empty#r289:{VV#545 : Data.ByteString.Lazy.Internal.ByteString | 
                                                 [(lbLength([VV#545]) = 0)
                                                 ; true
                                                 ; (lbLength([VV#545]) >= 0)]}
      ; Data.ByteString.Lazy.Internal.Chunk#r288:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.unsafeCreate#r1Ju:{VV : func(0, [int ; func(0, [GHC.Ptr.Ptr int ; GHC.Types.IO fix##40##41#]) ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.nullForeignPtr#r1Jr:{VV#485 : GHC.ForeignPtr.ForeignPtr int | 
                                                     [(fplen([VV#485]) = 0)]}
      ; Data.ByteString.Internal.memset#r1JP:{VV : func(0, [GHC.Ptr.Ptr int ; int ; int ; GHC.Types.IO (GHC.Ptr.Ptr int)]) | []}
      ; Data.ByteString.Internal.memcpy#r1JM:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.memcmp#r1JL:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.create#r1Jv:{VV : func(0, [int ; func(0, [GHC.Ptr.Ptr int ; GHC.Types.IO fix##40##41#]) ; GHC.Types.IO Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.c_reverse#r1JQ:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.c_minimum#r1JT:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.c_maximum#r1JS:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.c_intersperse#r1JR:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.PS#r1FG:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Fusion.scanEFL#r2ap:{VV : func(0, [func(0, [int ; int ; int]) ; int ; int ; Data.ByteString.Fusion.PairS int (Data.ByteString.Fusion.MaybeS int)]) | []}
      ; Data.ByteString.Fusion.mapIndexEFL#r2ar:{VV : func(0, [func(0, [int ; int ; int]) ; int ; int ; Data.ByteString.Fusion.PairS int (Data.ByteString.Fusion.MaybeS int)]) | []}
      ; Data.ByteString.Fusion.liquidCanaryFusion#r2aj:{VV : func(0, [int ; int]) | []}] 
 grd true 
 lhs {VV#F2169 : int | [(VV#F2169 = (n#a3su + lq_anf__d3Nu))
                       ; (VV#F2169 = lq_anf__d3Nv)]} 
 rhs {VV#F2169 : int | [k_1995[x#a3st:=fix#x#39##35#a3sw][p#a3ss:=lq_anf__d3Nt][ds_d3JQ:=lq_anf__d3Nr][VV#F:=VV#F2169][VV#1994:=VV#F2169][VV#12295:=VV#F2169]
                       ; (VV#F2169 < n#a3su); (VV#F2169 >= 0)]} 
 id 2169 tag [55] // 


constraint:
 env  [ x#a3se:{VV#3958 : a_tv | [k_3959]}
      ; unfoldChunk#a3Ed:{VV : func(0, [int ; int ; a_tv ; List Data.ByteString.Internal.ByteString]) | []}
      ; ttrd:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(2)]) | []}
      ; tsnd:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(1)]) | []}
      ; tfst:{VV : func(3, [fix##40##41# @(0) @(1) @(2) ; @(0)]) | []}
      ; sumLens:{VV : func(1, [List (List @(0)) ; int]) | []}
      ; snd:{VV : func(2, [fix##40##41# @(0) @(1) ; @(1)]) | []}
      ; s#a3sf:{VV#3976 : Data.ByteString.Internal.ByteString | [true
                                                                ; (bLength([VV#3976]) <= n#a3sc)
                                                                ; (0 <= bLength([VV#3976]))]}
      ; psnd:{VV : func(2, [Data.ByteString.Fusion.PairS @(0) @(1) ; @(1)]) | []}
      ; plen:{VV : func(1, [GHC.Ptr.Ptr @(0) ; int]) | []}
      ; pfst:{VV : func(2, [Data.ByteString.Fusion.PairS @(0) @(1) ; @(0)]) | []}
      ; pbase:{VV : func(1, [GHC.Ptr.Ptr @(0) ; int]) | []}
      ; papp2:{VV : func(4, [Pred @(0) @(1) ; @(2) ; @(3) ; bool]) | []}
      ; papp1:{VV : func(2, [Pred @(0) ; @(1) ; bool]) | []}
      ; null:{VV : func(1, [List @(0) ; bool]) | []}
      ; n#a3sc:{VV#3954 : int | [k_3955]}
      ; lq_anf__d3QS:{VV#3998 : int | [(VV#3998 = (n#a3sc + fix#n#39##35#a3sd))]}
      ; lq_anf__d3QQ:{VV#3977 : Data.Maybe.Maybe a_tv | [(isJust(VV#3977) => (bLength([s#a3sf]) = n#a3sc))
                                                        ; (VV#3977 = ds_d3KR)
                                                        ; (VV#3977 = Data.Maybe.Just#r1a([fix#x#39##35#a3sh]))
                                                        ; (fromJust([VV#3977]) = fix#x#39##35#a3sh)
                                                        ; (isJust(VV#3977) <=> true)]}
      ; lq_anf__d3QP:{VV#3973 : fix##40##41# Data.ByteString.Internal.ByteString (Data.Maybe.Maybe a_tv) | 
                     [(VV#3973 = lq_anf__d3QO)
                     ; (VV#3973 = fix#GHC.Tuple.#40##44##41##35#74([s#a3sf; ds_d3KR]))
                     ; (snd([VV#3973]) = ds_d3KR); (fst([VV#3973]) = s#a3sf)]}
      ; lq_anf__d3QO:{VV#3973 : fix##40##41# Data.ByteString.Internal.ByteString (Data.Maybe.Maybe a_tv) | []}
      ; len:{VV : func(1, [List @(0) ; int]) | []}
      ; lbLengths:{VV : func(0, [List Data.ByteString.Lazy.Internal.ByteString ; int]) | []}
      ; lbLength:{VV : func(0, [Data.ByteString.Lazy.Internal.ByteString ; int]) | []}
      ; isNullPtr:{VV : func(1, [GHC.Ptr.Ptr @(0) ; bool]) | []}
      ; isJustS:{VV : func(1, [Data.ByteString.Fusion.MaybeS @(0) ; bool]) | []}
      ; isJust:{VV : func(1, [Data.Maybe.Maybe @(0) ; bool]) | []}
      ; fst:{VV : func(2, [fix##40##41# @(0) @(1) ; @(0)]) | []}
      ; fromJust:{VV : func(1, [Data.Maybe.Maybe @(0) ; @(0)]) | []}
      ; fplen:{VV : func(1, [GHC.ForeignPtr.ForeignPtr @(0) ; int]) | []}
      ; fix#x#39##35#a3sh:{VV#3971 : a_tv | [k_3972[x:=fix#x#39##35#a3sh][lq_tmp_db78:=x#a3se][lq_tmp_db76:=f#a3sa][i:=n#a3sc][b:=ds_d3KR][a:=s#a3sf][VV#3977:=lq_anf__d3QQ][VV#3973:=lq_anf__d3QP][VV:=lq_anf__d3QQ]]}
      ; fix#n#39##35#a3sd:{VV#3956 : int | [k_3957]}
      ; fix#GHC.Types.#91##93##35#6m:{VV : func(1, [List @(0)]) | []}
      ; fix#GHC.Types.#58##35#64:{VV : func(1, [@(0) ; List @(0) ; List @(0)]) | []}
      ; fix#GHC.Tuple.#40##44##44##41##35#76:{VV : func(3, [@(0) ; @(1) ; @(2) ; fix##40##41# @(0) @(1) @(2)]) | []}
      ; fix#GHC.Tuple.#40##44##41##35#74:{VV : func(2, [@(0) ; @(1) ; fix##40##41# @(0) @(1)]) | []}
      ; fix#GHC.Tuple.#40##41##35#70:{VV : fix##40##41# | []}
      ; fix#GHC.Prim.#43##35##35#98:{VV : func(0, [int ; int ; int]) | []}
      ; fix#GHC.Prim.#40##35##44##35##41##35#84:{VV : func(2, [@(0) ; @(1) ; fix##40##41# @(0) @(1)]) | []}
      ; fix#GHC.Classes.D#58#Ord#35#rZT:{VV : func(1, [GHC.Classes.Eq @(0) ; func(0, [@(0) ; @(0) ; GHC.Types.Ordering]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; @(0)]) ; func(0, [@(0) ; @(0) ; @(0)]) ; GHC.Classes.Ord @(0)]) | []}
      ; fix#GHC.Classes.D#58#Eq#35#r11x:{VV : func(1, [func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; func(0, [@(0) ; @(0) ; GHC.Types.Bool]) ; GHC.Classes.Eq @(0)]) | []}
      ; fix#GHC.Classes.#38##38##35#r1e:{VV : func(0, [GHC.Types.Bool ; GHC.Types.Bool ; GHC.Types.Bool]) | []}
      ; fix#Data.ByteString.foldr1#39##35#r2WQ:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; fix#Data.ByteString.foldl1#39##35#r2WO:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; fix#Data.ByteString.Lazy.Internal.#36#WChunk#35#r28N:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString]) | []}
      ; fix#Data.ByteString.Internal.#36#WPS#35#r1Pa:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; fix##36##36##39##58##39#:{VV : GHC.Prim.Char# | []}
      ; fix##36##36##39##32##39#:{VV : GHC.Prim.Char# | []}
      ; fix##36##36##34#tail#34#:{VV : int | []}
      ; fix##36##36##34#minimum#34#:{VV : int | []}
      ; fix##36##36##34#maximum#34#:{VV : int | []}
      ; fix##36##36##34#last#34#:{VV : int | []}
      ; fix##36##36##34#init#34#:{VV : int | []}
      ; fix##36##36##34#head#34#:{VV : int | []}
      ; fix##36##36##34#foldr1#34#:{VV : int | []}
      ; fix##36##36##34#foldl1#39##34#:{VV : int | []}
      ; fix##36##36##34#foldl1#34#:{VV : int | []}
      ; fix##36##36##34#empty#32#ByteString#34#:{VV : int | []}
      ; fix##36##36##34#LIQUIDCOMPAT#34#:{VV : int | []}
      ; fix##36##36##34#Data.ByteString.#34#:{VV : int | []}
      ; fix##36##36##34#Data#47#ByteString.split.0.T.hs#58#358#58#21#45#26#34#:
        {VV : int | []}
      ; fix##36##36##34#Data#47#ByteString.split.0.T.hs#58#351#58#19#45#24#34#:
        {VV : int | []}
      ; f#a3sa:{VV : func(0, [a_tv ; Data.Maybe.Maybe (fix##40##41# int a_tv)]) | []}
      ; eta_B1:{VV : func(0, [a_tv ; Data.Maybe.Maybe (fix##40##41# int a_tv)]) | []}
      ; ds_d3KR:{VV#3977 : Data.Maybe.Maybe a_tv | [(isJust(VV#3977) => (bLength([s#a3sf]) = n#a3sc))]}
      ; deref:{VV : func(1, [GHC.Ptr.Ptr @(0) ; @(0)]) | []}
      ; cmp:{VV : func(0, [GHC.Types.Ordering ; GHC.Types.Ordering]) | []}
      ; cStringLen:{VV : func(0, [fix##40##41# (GHC.Ptr.Ptr Foreign.C.Types.CChar) int ; int]) | []}
      ; bPayload:{VV : func(0, [Data.ByteString.Internal.ByteString ; GHC.ForeignPtr.ForeignPtr int]) | []}
      ; bOffset:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; bLengths:{VV : func(0, [List Data.ByteString.Internal.ByteString ; int]) | []}
      ; bLength:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; addrLen:{VV : func(0, [int ; int]) | []}
      ; Set_sub:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; bool]) | []}
      ; Set_sng:{VV : func(1, [@(0) ; Set_Set @(0)]) | []}
      ; Set_mem:{VV : func(1, [@(0) ; Set_Set @(0) ; bool]) | []}
      ; Set_emp:{VV : func(1, [Set_Set @(0) ; bool]) | []}
      ; Set_dif:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Set_cup:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Set_cap:{VV : func(1, [Set_Set @(0) ; Set_Set @(0) ; Set_Set @(0)]) | []}
      ; Prop:{VV : func(0, [GHC.Types.Bool ; bool]) | []}
      ; GHC.Word.W8##r1dO:{VV : func(0, [GHC.Prim.Word# ; int]) | []}
      ; GHC.Types.True#6u:{VV : GHC.Types.Bool | []}
      ; GHC.Types.LT#6S:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.I##6c:{VV : func(0, [int ; int]) | []}
      ; GHC.Types.GT#6W:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.False#68:{VV : GHC.Types.Bool | []}
      ; GHC.Types.EQ#6U:{VV : GHC.Types.Ordering | []}
      ; GHC.Types.C##62:{VV : func(0, [GHC.Prim.Char# ; GHC.Types.Char]) | []}
      ; GHC.Ptr.Ptr#rO5:{VV : func(1, [int ; GHC.Ptr.Ptr @(0)]) | []}
      ; GHC.Prim.realWorld##0f:{VV#356 : GHC.Prim.State# GHC.Prim.RealWorld | []}
      ; GHC.Classes.not#r1d:{VV : func(0, [GHC.Types.Bool ; GHC.Types.Bool]) | []}
      ; GHC.CString.unpackCString##0k:{VV : func(0, [int ; List GHC.Types.Char]) | []}
      ; Data.Maybe.Nothing#r19:{VV : func(1, [Data.Maybe.Maybe @(0)]) | []}
      ; Data.Maybe.Just#r1a:{VV : func(1, [@(0) ; Data.Maybe.Maybe @(0)]) | []}
      ; Data.ByteString.unpackList#r2Ws:{VV : func(0, [Data.ByteString.Internal.ByteString ; List int]) | []}
      ; Data.ByteString.unpackFoldrINLINED#r2Wq:{VV : func(0, [Data.ByteString.Internal.ByteString ; List int]) | []}
      ; Data.ByteString.unpack#r2Wp:{VV : func(0, [Data.ByteString.Internal.ByteString ; List int]) | []}
      ; Data.ByteString.uncons#r2Wz:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.Maybe.Maybe (fix##40##41# int Data.ByteString.Internal.ByteString)]) | []}
      ; Data.ByteString.transpose#r2WG:{VV : func(0, [List Data.ByteString.Internal.ByteString ; List Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.takeWhile#r2Xb:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.take#r2X8:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.tail#r2Wy:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.splitAt#r2Xa:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.spanEnd#r2Xi:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.spanByte#r2Xh:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.span#r2Xg:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.sort#r2Xk:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.snoc#r2Ww:{VV : func(0, [Data.ByteString.Internal.ByteString ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.singleton#r2Wn:{VV : func(0, [int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanr1#r2X3:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanr#r2X2:{VV : func(0, [func(0, [int ; int ; int]) ; int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanl1#r2X1:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.scanl#r2X0:{VV : func(0, [func(0, [int ; int ; int]) ; int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.reverse#r2WE:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.replicate#r2X4:{VV : func(0, [int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.pack#r2Wo:{VV : func(0, [List int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.null#r2Wt:{VV : func(0, [Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.minimum#r2WW:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.maximum#r2WV:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.mapIndexed#r2WZ:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.map#r2WD:{VV : func(0, [func(0, [int ; int]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.lengths#r2Wg:{VV : func(0, [List Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.length#r2Wu:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.last#r2WA:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.intersperse#r2WF:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.intercalateWithByte#r2Xj:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.init#r2WB:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.head#r2Wx:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.foldr1#r2WP:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.foldl1#r2WN:{VV : func(0, [func(0, [int ; int ; int]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.findIndexOrEnd#r2Xl:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.findFromEndUntil#r2Xp:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.eq#r2Wk:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.empty#r2Wm:{VV#290 : Data.ByteString.Internal.ByteString | 
                                   [true; (bLength([VV#290]) = 0)
                                   ; (0 <= bLength([VV#290]))]}
      ; Data.ByteString.elemIndex#r2Wj:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.Maybe.Maybe int]) | []}
      ; Data.ByteString.dummyForQuals2_splitWith#r2Wi:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.dummyForQuals1_elemIndex#r2Wh:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO (GHC.Ptr.Ptr int)]) | []}
      ; Data.ByteString.dropWhile#r2Xc:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.drop#r2X9:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.cons#r2Wv:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.concatMap#r2WS:{VV : func(0, [func(0, [int ; Data.ByteString.Internal.ByteString]) ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.concat#r2WR:{VV : func(0, [List Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.breakEnd#r2Xf:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.breakByte#r2Xe:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.break#r2Xd:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; fix##40##41# Data.ByteString.Internal.ByteString Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.append#r2WC:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.any#r2WT:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.all#r2WU:{VV : func(0, [func(0, [int ; GHC.Types.Bool]) ; Data.ByteString.Internal.ByteString ; GHC.Types.Bool]) | []}
      ; Data.ByteString.Unsafe.unsafeTake#r1ZE:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Unsafe.unsafeTail#r1ZC:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Unsafe.unsafeHead#r1ZB:{VV : func(0, [Data.ByteString.Internal.ByteString ; int]) | []}
      ; Data.ByteString.Unsafe.unsafeDrop#r1ZF:{VV : func(0, [int ; Data.ByteString.Internal.ByteString ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Lazy.Internal.Empty#r289:{VV#545 : Data.ByteString.Lazy.Internal.ByteString | 
                                                 [(lbLength([VV#545]) = 0)
                                                 ; true
                                                 ; (lbLength([VV#545]) >= 0)]}
      ; Data.ByteString.Lazy.Internal.Chunk#r288:{VV : func(0, [Data.ByteString.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString ; Data.ByteString.Lazy.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.unsafeCreate#r1Ju:{VV : func(0, [int ; func(0, [GHC.Ptr.Ptr int ; GHC.Types.IO fix##40##41#]) ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.nullForeignPtr#r1Jr:{VV#485 : GHC.ForeignPtr.ForeignPtr int | 
                                                     [(fplen([VV#485]) = 0)]}
      ; Data.ByteString.Internal.memset#r1JP:{VV : func(0, [GHC.Ptr.Ptr int ; int ; int ; GHC.Types.IO (GHC.Ptr.Ptr int)]) | []}
      ; Data.ByteString.Internal.memcpy#r1JM:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.memcmp#r1JL:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.create#r1Jv:{VV : func(0, [int ; func(0, [GHC.Ptr.Ptr int ; GHC.Types.IO fix##40##41#]) ; GHC.Types.IO Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Internal.c_reverse#r1JQ:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.c_minimum#r1JT:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.c_maximum#r1JS:{VV : func(0, [GHC.Ptr.Ptr int ; int ; GHC.Types.IO int]) | []}
      ; Data.ByteString.Internal.c_intersperse#r1JR:{VV : func(0, [GHC.Ptr.Ptr int ; GHC.Ptr.Ptr int ; int ; int ; GHC.Types.IO fix##40##41#]) | []}
      ; Data.ByteString.Internal.PS#r1FG:{VV : func(0, [GHC.ForeignPtr.ForeignPtr int ; int ; int ; Data.ByteString.Internal.ByteString]) | []}
      ; Data.ByteString.Fusion.scanEFL#r2ap:{VV : func(0, [func(0, [int ; int ; int]) ; int ; int ; Data.ByteString.Fusion.PairS int (Data.ByteString.Fusion.MaybeS int)]) | []}
      ; Data.ByteString.Fusion.mapIndexEFL#r2ar:{VV : func(0, [func(0, [int ; int ; int]) ; int ; int ; Data.ByteString.Fusion.PairS int (Data.ByteString.Fusion.MaybeS int)]) | []}
      ; Data.ByteString.Fusion.liquidCanaryFusion#r2aj:{VV : func(0, [int ; int]) | []}] 
 grd true 
 lhs {VV#F1290 : int | [k_3957[VV#F:=VV#F1290][VV#3956:=VV#F1290][VV#10134:=VV#F1290]
                       ; (VV#F1290 = fix#n#39##35#a3sd)]} 
 rhs {VV#F1290 : int | [k_3955[VV#F:=VV#F1290][VV#3954:=VV#F1290][VV#10134:=VV#F1290]
                       ; (VV#F1290 < n#a3sc); (VV#F1290 >= 0)]} 
 id 1290 tag [72] // 
Fixpoint: Saving Result 
Fixpoint: Saving Result DONE 
Fixpoint Solver Time 
TOTAL                         796.614 s
  save                           0.680 s
  solve                         428.419 s
    Solve.unsatcs                  9.005 s
      Z3.pop                         0.148 s
      unsat                          0.516 s
        Z3.check                       0.516 s
      Z3.ass_cst                     0.532 s
      Z3.push                        1.144 s
      z3Pred                         4.292 s
        z3Var memo                     0.700 s
      fixdiv                         0.072 s
    Solve.dump                     0.108 s
    Solve.acsolve                 418.434 s
      refine                        415.482 s
        refine                        415.474 s
          cx_update                      0.000 s
          check tp                      402.845 s
            Z3.pop                        17.525 s
            unsat                         353.318 s
              Z3.check                      352.290 s
            Z3.ass_cst                    12.557 s
            Z3.push                        5.260 s
            z3Pred                         9.417 s
              z3Var memo                     2.176 s
            fixdiv                         0.272 s
          lhs_contra                     0.020 s
          preds_of_lhs                   7.769 s
          rhs_cands                      4.704 s
    Cindex.winit                   0.008 s
    Prepass.profile                0.332 s
  Validate                      58.392 s
    valid rhs                      5.720 s
      validate_vars                  1.392 s
      preds_of_reft                  3.448 s
    validate_vars                  4.844 s
  cx_update                      0.196 s
  Z3.check                       0.000 s
  Z3 assert axiom                0.000 s
  z3Var memo                     0.000 s
  Constant EnvWF                 0.152 s
  Simplify                       0.004 s
    add ids  1                     0.004 s
  Constant Env                   0.180 s
  Ref Index                      0.000 s
  create                         0.000 s
  making_graph                   0.404 s
  parse                          1.984 s
  Annots: make qleqs             0.112 s
    Z3.pop                         0.008 s
    unsat                          0.064 s
      Z3.check                       0.064 s
    Z3.ass_cst                     0.012 s
    Z3.push                        0.008 s
    z3Pred                         0.008 s
      z3Var memo                     0.004 s
    fixdiv                         0.004 s
    Z3.check                       0.000 s
    Z3 assert axiom                0.000 s
    z3Var memo                     0.000 s
  Qual Inst                     306.091 s

UNSAT

****************************** DONE:  fixpoint *****************************

****************************** DONE:  solve *****************************
WARNING: Found false in Data/ByteString.split.0.T.hs:1033:57-65
WARNING: Found false in Data/ByteString.split.0.T.hs:1034:28
WARNING: Found false in Data/ByteString.split.0.T.hs:1034:55
WARNING: Found false in Data/ByteString.split.0.T.hs:1036:12
WARNING: Found false in Data/ByteString.split.0.T.hs:1036:14
WARNING: Found false in Data/ByteString.split.0.T.hs:1036:18
WARNING: Found false in Data/ByteString.split.0.T.hs:1036:26
WARNING: Found false in Data/ByteString.split.0.T.hs:1036:26-38
WARNING: Found false in Data/ByteString.split.0.T.hs:1038:25
WARNING: Found false in Data/ByteString.split.0.T.hs:1038:46
WARNING: Found false in Data/ByteString.split.0.T.hs:1039:25-82
WARNING: Found false in Data/ByteString.split.0.T.hs:1039:31
WARNING: Found false in Data/ByteString.split.0.T.hs:1039:48-50
WARNING: Found false in Data/ByteString.split.0.T.hs:1039:66
WARNING: Found false in Data/ByteString.split.0.T.hs:1039:69
WARNING: Found false in Data/ByteString.split.0.T.hs:1040:25-67
WARNING: Found false in Data/ByteString.split.0.T.hs:1040:29
WARNING: Found false in Data/ByteString.split.0.T.hs:1040:37-39
WARNING: Found false in Data/ByteString.split.0.T.hs:1040:65
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:22
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:24
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:26
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:30
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:38
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:38-58
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:46
WARNING: Found false in Data/ByteString.split.0.T.hs:1047:46-58
WARNING: Found false in Data/ByteString.split.0.T.hs:1050:12
WARNING: Found false in Data/ByteString.split.0.T.hs:1050:16
WARNING: Found false in Data/ByteString.split.0.T.hs:1051:16
WARNING: Found false in Data/ByteString.split.0.T.hs:1051:21-23
WARNING: Found false in Data/ByteString.split.0.T.hs:1052:31
WARNING: Found false in Data/ByteString.split.0.T.hs:1052:68-70
WARNING: Found false in Data/ByteString.split.0.T.hs:1052:72
WARNING: Found false in Data/ByteString.split.0.T.hs:1053:31
WARNING: Found false in Data/ByteString.split.0.T.hs:1053:48-53
WARNING: Found false in Data/ByteString.split.0.T.hs:1053:55
WARNING: Found false in Data/ByteString.split.0.T.hs:1054:43-48
WARNING: Found false in Data/ByteString.split.0.T.hs:1054:50
WARNING: Found false in Data/ByteString.split.0.T.hs:1054:53
WARNING: Found false in Data/ByteString.split.0.T.hs:1055:31-40
WARNING: Found false in Data/ByteString.split.0.T.hs:1055:35
WARNING: Found false in Data/ByteString.split.0.T.hs:1083:16-18
WARNING: Found false in Data/ByteString.split.0.T.hs:1083:34-36
WARNING: Found false in Data/ByteString.split.0.T.hs:1087:13-15
WARNING: Found false in Data/ByteString.split.0.T.hs:1087:52-54

****************************** DONE:  annotate *****************************

****************************** DONE:  Unsafe: *****************************

****************************** WARNING: Data/ByteString.split.0.T.hs:823:45-46 *****************************

****************************** WARNING: Data/ByteString.split.0.T.hs:848:70-72 *****************************

****************************** Termination Warnings: *****************************
Data/ByteString.split.0.T.hs:564:9-10: No decreasing parameter
Data/ByteString.split.0.T.hs:541:9-10: No decreasing parameter
Data/ByteString.split.0.T.hs:510:9-11: No decreasing parameter
Data/ByteString.split.0.T.hs:1093:1-16: No decreasing parameter
Data/ByteString.split.0.T.hs:664:9-10: No decreasing parameter
Data/ByteString.split.0.T.hs:647:9-10: No decreasing parameter


