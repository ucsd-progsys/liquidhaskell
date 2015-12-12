TODO
====


Organizing Modules
------------------

+ Types
  + Names.hs
  + Variance.hs
  + Dictionaries.hs
  + Literals.hs
  + Strata.hs
  + Visitors.hs
  + Bounds.hs
  + RefType.hs
  + Types.hs
  + PredType.hs

+ GHC
  + GhcPlay.hs
  + GhcInterface.hs
  + GhcMisc.hs

+ Bare

+ UX
  + ACSS.hs
  + Annotate.hs
  + DiffCheck.hs
  + CTags
  + Tidy
  + Server.hs
  + CTags.hs
  + Config.hs
  + Tidy.hs
  + Cabal.hs
  + Errors.hs
  ? PrettyPrint.hs
  + CmdLine.hs

+ Transforms
  + ANFTransform
  + CoreToLogic.hs
  + Simplify.hs
  + TransformRec.hs
  + ANFTransform.hs
  ? RefSplit.hs

+ Constraints
  + Fresh.hs

+ Bare
  + Measure.hs

Liquid.hs
Misc.hs
WiredIn.hs
Parse.hs


Check covariants
----------------

See https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/todo/kmpMonad.hs#L55
It is safe is 100 is changed to 0. WHY?

LAZYVAR
-------
Restore LAZYVARS in `Data/Text.hs`, `Data/Text/Unsafe.hs`


Automatically refine *inductors*
--------------------------------
Proposed by Valentine: in dependent languages (Coq) inductors (like our `loop` for natural numbers)
automatically get types abstracted over properties.
Trasversal should create such functions. Maybe we can automatically refine them.

Check refinements using `Eq` and `Ord` info
-------------------------------------------
Currenly we arbitrary allow `=` and comparison operators in refinements to arbitraty types.
This can lead to non-well formed refinements.

promotion of haskell functions to measures
------------------------------------------

+ test that promotion happens on proper functions (inductive with 1 ADT argument)
+ make sure that user and derived signature are met
+ make Haskell's function post conditions invariants

benchmarks
-----------

* benchmarks: Data.Bytestring
    ? readsPrec
    ? big constants issue : _word64 34534523452134213524525 due to (deriving Typeable)
    - see others below

* hmatrix

* error messages (see issues on github)

remove-parens
-------------

+ x16 to v
+ Range {0} {100} -- allow Range 0 100 instead.
+ extra PARENS in refinement printout.
+ qualifier duplication



exists-based constraints
------------------------

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



vector
------

Wordcount for vector

    1476 ./Vector/Fusion/Stream/Monadic.hs
      87 ./Vector/Fusion/Stream/Size.hs
     634 ./Vector/Fusion/Stream.hs
      57 ./Vector/Fusion/Util.hs
     142 ./Vector/Generic/Base.hs
     884 ./Vector/Generic/Mutable.hs
     172 ./Vector/Generic/New.hs
    2027 ./Vector/Generic.hs
     163 ./Vector/Internal/Check.hs
     398 ./Vector/Mutable.hs
     332 ./Vector/Primitive/Mutable.hs
    1328 ./Vector/Primitive.hs
      45 ./Vector/Storable/Internal.hs
     490 ./Vector/Storable/Mutable.hs
    1421 ./Vector/Storable.hs
     389 ./Vector/Unboxed/Base.hs
     285 ./Vector/Unboxed/Mutable.hs
    1368 ./Vector/Unboxed.hs
    1510 ./Vector.hs
   13208 total


Dependency order for vector

[ 1 of 19]  [45]      Data.Vector.Storable.Internal
[ 2 of 19]  [57]      Data.Vector.Fusion.Util
[ 4 of 19]  [163]     Data.Vector.Internal.Check
[ 3 of 19]  [87]      Data.Vector.Fusion.Stream.Size      (SKIP:STREAM?)
[ 5 of 19]  [1476]    Data.Vector.Fusion.Stream.Monadic   (SKIP:STREAM?)
[ 6 of 19]  [634]     Data.Vector.Fusion.Stream           (SKIP:STREAM?)
[ 7 of 19]  [884]     Data.Vector.Generic.Mutable
[ 8 of 19]  [142]     Data.Vector.Generic.Base            (REDO: no class instances...)
[ 9 of 19]  [172]     Data.Vector.Generic.New             (TODO:FORALL/APP/github issue #202)

HEREHEREHERE

[10 of 19]  [2027]    Data.Vector.Generic
[11 of 19]  [332]     Data.Vector.Primitive.Mutable
[12 of 19]  [1328]    Data.Vector.Primitive
[13 of 19]  [490]     Data.Vector.Storable.Mutable
[14 of 19]  [1421]    Data.Vector.Storable
[15 of 19]  [389]     Data.Vector.Unboxed.Base
[16 of 19]  [1368]    Data.Vector.Unboxed
[17 of 19]  [285]     Data.Vector.Unboxed.Mutable
[18 of 19]  [398]     Data.Vector.Mutable
[19 of 19]  [1510]    Data.Vector




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

+ Create a test case: `tests/todo/Eff*.hs`

+ Introduce a new sort of refinement `Ref` (with alias `RTProp`)
   + Types.hs: Add to `Ref` -- in addition to `RMono` [---> `RPropP`] and `RPoly` [---> `RProp`]
   + Types.hs: Add a `World t` for SL formulas...


+ Allow `PVar` to have the sort `HProp`
   + CHANGE `ptype :: PVKind t` where `data PVKind t = PVProp t | PVHProp`
   + Can we reuse `RAllP` to encode `HProp`-quantification? (YES)
   + Update `RTyCon` to store `HProp` vars

- Update consgen
   + Can we reuse type-application sites for `HProp`-instantiation? (Yes)
   - Constraint.hs  :1642:   = errorstar "TODO:EFFECTS:freshPredRef"
   - PredType.hs         : go _ (_, RHProp _ _)    = errorstar "TODO:EFFECTS:replacePreds"

- Write cons-solve
  - eliminate/solve `HProp` constraints prior to subtype splitting.

- Index `IO` or `State` by `HProp`
   - Parse.hs: Update `data` parser to allow `TyCon` to be indexed by abstract `HProp`
   - Bare.hs        :482 : addSymSortRef _ (RHProp _ _)   = errorstar "TODO:EFFECTS:addSymSortRef"

**TODO:EFFECTS:ASKNIKI**
+ What is `isBind`,`pushConsBind` in Constraint.hs?


3. Suitable signatures for monadic operators

### RHProp

a. Following `RProp` we should have

	* RHProp := x1:t1,...,xn:tn -> World

b. Where `World` is a _spatial conjunction_ of

	* WPreds : (h v1 ... vn), h2, ...
	* Wbinds : x1 := T1, x2 := T2, ...

c. Such that each `World` has _at most one_ `WPred` (that is _not rigid_ i.e. can be solved for.)

**Problem:** rejigger _inference_ to account for parameters in heap variables.



### RPoly  (---> RProp)

Per Niki:

	RProp := x1:t1,...,xn:tn -> RType

with the 'predicate' application implicitly buried as a `ur_pred` inside the RType

For example, we represent

	[a]<p>

as

	RApp [] a (RPoly  [(h:a)] {v:a<p>}) true

which is the `RTycon` for lists `[]` applied to:

+ Tyvar `a`

+ RPoly with:
	* _params_ `h:a`
	* _body_   `{v:a<p> | true}` which is really, `RVar a {ur_reft = true, ur_pred = (Predicate 'p' with params 'h')}`

+ Outer refinement `true`







**Heap Propositions** `HProp`

```haskell
CP := l :-> T * CP  -- Concrete Heap
    | emp

HP := CP       
    | CP * H        -- Heap Variable
```

That is, an `HProp` is of the form:

    H * l1 |-> T1 * ... * ln |-> Tn

or

    l1 |-> T1 * ... * ln |-> Tn

I am disallowing multiple variables because it causes problems...


**Abstractly Refined ST/IO**

```haskell
data IO a <Pre :: HProp, Post :: a -> HProp>
```

**Refined Monadic Operators**

```haskell
return :: forall a, <H :: HProp>.
            a -> IO <H, \_ -> H> a

(>>=)  :: forall a, b, <P :: HProp, Q :: a -> HProp, R :: b -> HProp>.
            IO<P, Q> a -> (x:a -> IO<Q x, R> b) -> IO<P, R> b
```

**Q1.** How does LH *reason* about `HProp`?

Via subtyping as always, so:

         forall i. Γ |- Ti <: Ti'
    -----------------------------------
    Γ |- *_i li :-> Ti <: *_i li -> Ti'

For this, we need to put in explicit `HProp` instantiations, just like
tyvar (α) and  predvar (π) instinstatntiations. This is doable with a
pre-pass that generates and solves `HProp` constraints as follows:

1. At each instantiation, make up _fresh_ variables `h`
2. Treat _bound_ heap-variables as **constants**
3. Instantiation yields a set of constraints over `h`
4. Solve constraints via algorithm below.

**Q2.** Can you _name_ values inside `HProp`?

Nope. There's no reason for this, but its tedious to have to make up
new heap binders and what not. Clutters stuff. This is _slightly_
problematic. For example, how do you write a function of the form:

```haskell
incr :: p:IORef Int -> IO Int
```

which _increments_ the value stored at the reference? Solution is slightly
clunky: rather than the _implicit_ heap binder, add an explicit pure parameter:

```haskell
incr :: p:IORef Int -> i:Int -> IO {v:Int| v = i} <p |-> {v = i}, p |-> {v = i + 1}>
```

**Q3.** How to relate `Post`-condition to the `Pre`-conditions?

Note that the `Post`-condition is a unary predicate -- i.e. _does not_
refer to the input world. How then do we relate the input and output heaps?
As above: _name_ the values of the input heap that you care about, and then
relate `Post` to `Pre` via the name.

**Q4.** How to _read_ values off the heap?

Given that we don't have heap binders, this might seem like a problem? Not
really. Just write signatures like:

    read :: IORef a -> IO a

aha, but there's a problem: the `a` is too _coarse_ or flow-insensitive: it
holds a supertype of all the values written at the location, as opposed to the
_current_ value. No matter, abstract refinements to the rescue:

    read :: forall <I :: a -> Prop>.
              p:IORef a -> IO <p |-> a<I>, p |-> a<I>> a<I>

**Q5.** How do you do _subtyping_ on heaps/frame rule?

Wait, how do I write _compositional_ signatures that only talk about a
particular part of the state but allow me to say _other_ parts are unmodified
etc? Don't you need heap subtyping? No: we can make the frame rule explicit by
abstracting over heaps:

    read :: forall <I :: a -> Prop, H :: HProp>.
              p:IORef a -> IO <p |-> a<I> * H, p |-> a<I> * H> a<I>

**Q6.** How to solve heap constraints?

Heap constraints are of the form:

+ (C0)  `ch1      = ch2`        -- constants
+ (C1)  `H1 * ch1 = ch2`        -- 1-variable
+ (C2)  `H1 * ch1 = H2 * ch2`   -- 2-variable

Here, each `ch` is of the form:

    l1 |-> τ1 * ... * ln -> τn * A1 * ... * An

where each `Ai` is a _rigid_ or quantified heap var that is atomic,
i.e. cannot be further solved for. For solving, we throw away _all_
refinements, and just use the shape τ.

```
solve :: Sol -> [Constraint] -> Maybe Sol
solve σ []     
  = Just σ
solve σ (c:cs)
  = case c of
      C0 ch1 ch2 ->
        if ch1 `equals` ch2  then
          -- c is trivially SAT,
          solve σ cs
        else
          -- c and hence all constraints are unsat
          Nothing

      C1 (H1 * ch1) ch2 ->
        if ch1 `subset` ch2 then
          let σ' = [H1 := c2 `minus` c1]
          solve (σ . σ') (σ' <$> cs)
        else
          -- c and hence all constraints are unsat
          Nothing

      C2 (H1 * ch1) (H2 * ch2) ->
        let H = fresh heap variable
        let σ'  = [H1 := H * ch2, H2 := H * ch1]
        solve (σ . σ') (σ' <$> cs)
```



PROJECT: (OLD) HTT style ST/IO reasoning with Abstract Refinements
------------------------------------------------------------------


Can we use abstract refinements to do "stateful reasoning",
e.g. about stuff in `IO` ? For example, to read files, this
is the API:

    open  :: FilePath -> IO Handle
    read  :: Handle   -> IO String
    write :: Handle   -> String -> IO ()
    close :: Handle   -> IO ()

The catch is that:

+ `read` and `write` require the `Handle` to be in an "open" state,
+ which is the state of the `Handle` returned by `open`,
+ while `close` presumably puts the `Handle` in a "closed" state.

So, suppose we parameterize IO with two predicates a `Pre` and `Post` condition

    data IO a <Pre :: World -> Prop> <Post :: a -> World -> World -> Prop>

where `World` is some abstract type denoting the global machine state.
Now, it should be possible to give types like:

   (>>=)  :: IO a <P, Q> -> (x:a -> IO b<Q x, R>) -> IO b<P, R>
   return :: a -> IO a <P, P>

which basically state whats going on with connecting the conditions, and then,
give types to the File API:

   open  :: FilePath -> IO Handle <\_ -> True> <\h _ w -> (IsOpen h w)>
   read  :: h:Handle -> IO String <\w -> (IsOpen h w)> <\_ _ w -> (IsOpen h w)>
   close :: h:Handle -> IO ()     <\w -> (IsOpen h w)> <\_ _ w -> not (IsOpen h w)>

Wonder if something like this would work?

Niki:
My question is how do you make Q from a post-condition (Q :: a -> Word -> Word -> Prop)
to a pre-condition.
I guess you need to apply a value x :: a and a w :: Word to write (a -> IO b<Q x w, R>).

I think the problem is that the "correct" values x and w are not "in scope"


So assume

    data IO a <P :: Word -> Prop, Q: a -> Word -> Word -> Prop>
      = IO (x:Word<P> -> (y:a, Word<Q y x>))

and you want to type

    bind :: IO a <P,Q> -> (a -> IO b <Q x w, R>) -> IO b <P,R>
    bind (IO m) k = IO $ \s -> case m s of
                                 (a, s') -> unIO (k a) s'


You have

    IO m :: IO a <P. Q> => m :: xx:Word <P> -> (y:a, Word <Q y xx>)

you can assume

    s:: Word <P>

so

    m s         :: (y:a, Word <Q y s>)
    k a         :: IO b <Q x w, R>
    uniIO (k a) :: z:Word <Q x w> -> (xx:b, Word <R xx z>)

and we want

    (uniIO k a) s :: (xx:b , Word <R xx s>)

so basically we need

    P  => Q x w

to be able to make the final application

**Ranjit**
You are right. We need to convert the "post" of the first action into the "pre"
of the second, which is a problem since the former takes three, parameters while
the latter takes only one.

BUT, how about this (basically, all you need is an EXISTS).

   -- | the type for `return` says that the output world satisfies
   --   whatever predicate the input world satisfied.

   return :: a -> IO a <P, {\_ _ w' -> (P w')}>

   -- | the type for `bind` says that its action requires as input a world that satisfies
   --   Q (for SOME input world w0) and produces as output an R world.
   (>>=)  :: IO a <P, Q>
          -> (x:a -> \exists w0:World. IO b<{\w -> (Q x w0 w)}, R>)
          -> IO b<P, {\xb w w' -> \exists xa:a w0:World<Q xa w>.(R xb w0 w')}>



Basically, I am using exists in the same way as in the "compose"

https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/funcomposition.hs

to name the intermediate worlds and results (after all, this seems
like a super fancy version of `.` ) -- may have not put them in the
right place...

Btw, the existential is also how the HOARE rule for strongest postcondition works,
if you recall:

   {P} x := e {exists x'. P[x'/x] /\ x = e[x'/x]}




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


bind :: ST a <P,Q> -> (a -> ST b <Q x w, R>) -> ST b <P,R>
bind (ST f1) k = ST $ \s0 -> let (x, s1) = f1 s0  
                                 ST f2   = k x
                                 (y, s2) = f2 s1
                             in
                                 (y, s2)


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


PROJECT: Equational Reasoning
-----------------------------

e.g. Type class laws.

Many type-classes come with a set of laws that instances are expected
to abide by, e.g.

```
fmap id  ==  id

fmap (f . g)  ==  fmap f . fmap g
```

```
mappend mempty x = x

mappend x mempty = x

mappend x (mappend y z) = mappend (mappend x y) z
```

**Strategy**

**1. Representing Proofs**

```
data Proof  = Proof           -- void, pure refinement

type Pf P   = {v:Proof | P}

type Eq X Y = Pf (X == Y)
```

**2. Combining Proofs**

```
bound Imp P Q R = P => Q => R

eq, imp :: (Imp P Q R) => Pf P -> Pf Q -> Pf R

refl    :: x:a -> Eq a x x
```

**3. Axiomatizing arithmetic**

```
add :: x:Int -> y:Int -> {z:Int | z = x + y} -> Eq (x + y) z
add x y z = auto
```


**Example 1: Arithmetic**

Lets drill in: how to represent the following "equational" proof in LH?

```
     (1 + 2) + (3 + 4)       -- e0

     { 1 + 2 == 3}

  == 3 + (3 + 4)             -- e1

     { 3 + 4 == 7}

  == 3 + 7                   -- e2

     { 3 + 7 == 10}

  == 10                      -- e3
```

Now the above proof looks like this:

```
e0 :: Int
e0 = (1 + 2) + (3 + 4)

prop :: Eq e0 10
prop = (((refl e0  `imp` (add 1 2 3))   -- :: Eq e0 (3 + (3 + 4))

                   `imp` (add 3 4 7))   -- :: Eq e0 (3 + 7)

                   `imp` (add 3 7 10))  -- :: Eq e0 10  
```


**Example 2: Lists**

A more interesting example: Lets prove `prop_app_nil`:

    prop_app_nil: forall xs. append xs [] = xs

The definition of

```
append []     ys = ys
append (x:xs) ys = x : append xs ys
```

yields the *axioms*

```
append_nil  :: ys:_ -> Eq (append [] ys) ys
append_cons :: x:_ -> xs:_ -> ys:_ -> Eq (append (x:xs) ys) (x : append xs ys)
```

Code on left, "equations" on right.

```
prop_app_nil    :: xs:[a] -> Eq (append xs []) xs

prop_app_nil []     = refl (append [] [])             
                                                   -- append [] []
                       `by` (append_nil [])        -- { append_nil [] }    
                                                   -- == []  

prop_app_nil (x:xs) = refl (append (x:xs) [])       
                                                   -- append (x:xs) []
                       `by` (append_cons x xs [])  -- { append_cons x xs [] }
                                                   -- == x : append xs []
                       `by` (prop_app_nil xs)      -- { IH: prop_app xs }
                                                   -- == x : xs
```

**Example 4: Append Associates**


```
prop_app_assoc :: xs:_ -> ys:_ -> zs:_ ->
                     Eq ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))

prop_app_assoc [] ys zs
  ([] ++ ys) ++ zs
  { append_nil _ }    
  == ys ++ zs
  { append_nil _ }
  == [] ++ (ys ++ zs)

prop_app_assoc (x:xs) ys zs
  ((x:xs) ++ ys) ++ zs
  { append_cons _ _ _ }    
  == (x : (xs ++ ys)) ++ zs
  { append_cons _ _ _ }
  == x : ((xs ++ ys) ++ zs)
  { prop_app_assoc _ _ _ }
  == x : (xs ++ (ys ++ zs))
  { append_cons _ _ _ }
  == (x : xs) ++ (ys ++ zs)
```


**Example 4: Map Fusion**

Lets go fancier:


    forall xs. map (f . g) xs = (map f . map g) xs

Here's the classical (?) equational proof:

```
map (f . g) []   
   { map_nil (f . g) }
   == []
   { map_nil f }
   == map f []
   { map_nil g }
   == map f (map g [])
   { dot f g }
   == (map f . map g) []

map (f . g) (x:xs)  
   { map_cons (f . g) x xs }
   == (f . g) x : map (f . g) xs
   { map_dot f g xs }
   == (f . g) x : (map f . map g) xs
   { dot (map f) (map g) }
   == (f . g) x : map f (map g xs)
   { dot f g }
   == f (g x) : map f (map g xs)
   {map_cons f (g x) (map g xs) }
   == map f (g x : map g xs)
   {map_cons g x xs}
   == map f (map g (x : xs))
   { dot (map f) (map g) }
   ==  (map f . map g) (x : xs)
```

Formalize thus (with functions/axioms)

```
map f []     = []               -- map_nil
map f (x:xs) = f x  : map f xs  -- map_cons

(f . g) x    =  f (g x)         -- dot
```

Now, we formalize map-fusion as:

```
map_fusion :: f:_ -> g:_ -> xs:_ ->
              Eq (map (f . g) xs) (map f . map g) xs

map_fusion f g []     = map_dot_nil f g
map_fusion f g (x:xs) = map_dot_cons f g x xs
```

The hard work happens in the two "lemmas"

```
map_dot_nil :: f:_ -> g:_ ->
               Eq (map (f . g) []) ((map f . map g) [])
map_dot_nil f g
  = refl (map (f . g) [])   
                              -- map (f . g) []
     `by` (map_nil (f . g))
                              -- == []
     `by` (map_nil f)
                              -- == map f []
     `by` (map_nil g)
                              -- == map f (map g [])
     `by` (dot f g)
                              -- == (map f . map g) []
```

and

```
map_dot_cons :: f:_ -> g:_ -> x:_ -> xs:_ ->
               Eq (map (f . g) (x:xs)) ((map f . map g) (x:xs))
map_dot_cons f g x xs
  = refl (map (f . g) (x:xs))
                                          -- map (f . g) (x : xs)
      `by` (map_cons (f . g) x xs)
                                          -- == (f . g) x : map (f . g) xs
      `by` (map_dot f g xs)
                                          -- == (f . g) x : (map f . map g) xs
      `by` (dot (map f) (map g))
                                          -- == (f . g) x : map f (map g xs)
      `by` (dot f g)
                                          -- == f (g x) : map f (map g xs)
      `by` (map_cons f (g x) (map g xs))
                                          -- == map f (g x : map g xs)
      `by` (map_cons g x xs)
                                          -- == map f (map g (x : xs))
      `by` (dot (map f) (map g))
                                          -- ==  (map f . map g) (x : xs)
```



GHC 7.10
--------

- **DONE** singleton type classes represented by newtype
  - tried to work around by translating

      foo `cast` (co :: a -> b ~ Foo)

    to

      D:Foo foo

    but it still breaks when we don't have an LH class decl
  - without LH class decl we never see D:Foo, so it doesn't go in CGEnv
  - SOLUTION: put ALL visible dict constructors in CGEnv

- `cast`s are used more often and we seem to lose information..
  - seems particularly problematic with ST

- srcloc annotations
  - -g adds SourceNotes, but the html output is borked
  - in particular, infix operators aren't annotated correctly (at all?)
  - are we missing some SrcLocs??
    - clearly not, if you look at the output of

          ghc -g -ddump-ds -dppr-ticks <file.hs>

      somewhere along our pipeline the ticks are either being dropped,
      or the SrcSpans don't quite match the way they used to...

- termination metrics are required in a few places where they were not previously
  - my guess is that ghc's behaviour for grouping functions in a `Rec` binder have changed
