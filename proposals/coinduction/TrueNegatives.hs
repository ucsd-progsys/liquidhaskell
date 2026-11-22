{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--fuel=2" @-}

module TrueNegatives where

import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- Common definitions
--------------------------------------------------------------------------------

{-@ type Nat = {v:Int | 0 <= v} @-}
{-@ type FalseProof = {v:() | false} @-}

data Stream a = (:>) { sheadS :: a, stailS :: Stream a } | StreamEnd
infixr 5 :>

{-@ measure isCons @-}
isCons :: Stream a -> Bool
isCons (_ :> _)  = True
isCons StreamEnd = False

{-@ type IStream a = {v:Stream a | isCons v} @-}
{-@ data Stream a = (:>) { sheadS :: a, stailS :: IStream a } | StreamEnd @-}

data Later a = Later { forceLater :: a }

data DelayedStream a = DSCons a (Later (DelayedStream a)) | DSNil

{-@ measure isDSCons @-}
isDSCons :: DelayedStream a -> Bool
isDSCons (DSCons _ _) = True
isDSCons DSNil        = False

{-@ type IDelayedStream a = {v:DelayedStream a | isDSCons v} @-}

--------------------------------------------------------------------------------
-- 1. Unsafe list head access
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively, Section 1.1.
--
-- EXPECTED: REJECT (REFINEMENT TYPE ERROR).
--
-- Attempts to access the head of a list without establishing non-emptiness.
-- This is an ordinary safety violation unrelated to coinductive reasoning.
--------------------------------------------------------------------------------

data L a
  = Nil
  | (:|) a (L a)

{-@ measure notEmpty @-}
notEmpty :: L a -> Bool
notEmpty Nil      = False
notEmpty (_ :| _) = True

{-@ type NEList a = {xs:L a | notEmpty xs} @-}

{-@ shead :: NEList a -> a @-}
shead :: L a -> a
shead (x :| _) = x

{-@ unsafe :: xs:L a -> a @-}
unsafe :: L a -> a
unsafe xs = shead xs

--------------------------------------------------------------------------------
-- 2. Indexed falseStream
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively, Section 2.0.
--
-- EXPECTED: REJECT (REFINEMENT TYPE ERROR AT INDEX ZERO).
--
-- The recursive call decreases the index i, but the base case i == 0 cannot
-- establish False.
--------------------------------------------------------------------------------

{-@ falseStreamI
      :: xs:IStream a
      -> i:{Int | 0 <= i}
      -> {v:() | false}
      / [i]
  @-}
falseStreamI :: Stream a -> Int -> ()
falseStreamI _ 0 = ()
falseStreamI (_ :> xs) i =
  falseStreamI xs (i - 1)

--------------------------------------------------------------------------------
-- 3. Indexed constructive falseProp
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively, Section 3.0.
--
-- EXPECTED: REJECT (REFINEMENT TYPE ERROR AT INDEX ZERO).
--
-- The indexed equality witness permits recursive descent on i, but cannot
-- establish False at index zero.
--------------------------------------------------------------------------------

data EqC a where
  EqRefl :: Int -> a -> Stream a -> Stream a -> (Int -> EqC a) -> EqC a

{-@ measure eqIdx :: EqC a -> Int @-}

{-@ data EqC a where
      EqRefl :: i:Nat
             -> x:a
             -> xs:Stream a
             -> ys:Stream a
             -> (j:{Nat | j < i} -> {v:EqC a | eqIdx v == j})
             -> {v:EqC a | eqIdx v == i}
@-}

{-@ falseProp
      :: i:Nat
      -> xs:Stream a
      -> ys:Stream a
      -> {v:EqC a | eqIdx v == i}
      -> {v:() | false}
      / [i]
@-}
falseProp :: Int -> Stream a -> Stream a -> EqC a -> ()
falseProp 0 _ _ _ = ()
falseProp i _ _ (EqRefl _ _ xs ys p) =
  falseProp (i - 1) xs ys (p (i - 1))

--------------------------------------------------------------------------------
-- 4. Non-decreasing prefix index in BadProof
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figure 13.
--
-- EXPECTED: REJECT (TERMINATION ERROR).
--
-- The prefix index k is passed unchanged in the recursive call, so the
-- termination metric does not decrease.
--------------------------------------------------------------------------------

{-@ reflect trivialK @-}
{-@ trivialK :: IStream a -> k:Nat -> Bool / [k] @-}
trivialK :: Stream a -> Int -> Bool
trivialK _ 0 = True
trivialK (_ :> xs) k = trivialK xs (k - 1)

{-@ badProof :: s:IStream a -> k:Nat -> {true} / [k] @-}
badProof :: Stream a -> Int -> Proof
badProof _ 0 = ()
badProof s@(_ :> _) k = badProof s k

--------------------------------------------------------------------------------
-- 5. Constructor immediately consumed by a destructor (list)
--
-- Sources:
--   Danielsson (2010), Beating the Productivity Checker Using Embedded
--   Languages, Section 1.
--
-- EXPECTED: REJECT (NON-PRODUCTIVE).
--
-- The cons constructor is immediately cancelled by tail; evaluating badTail
-- never exposes a constructor.
--------------------------------------------------------------------------------

badTail :: [Int]
badTail = tail (0 : badTail)

--------------------------------------------------------------------------------
-- 6. Constructor immediately consumed by a destructor (stream)
--
-- Sources:
--   Danielsson (2010), Beating the Productivity Checker Using Embedded
--   Languages, Section 1.
--
-- EXPECTED: REJECT (NON-PRODUCTIVE).
--
-- Although (:>) occurs syntactically, its result is immediately destroyed by
-- stailS. No constructor is ever exposed to an observer.
--------------------------------------------------------------------------------

{-@ badAfterDestructor :: IStream Int @-}
badAfterDestructor :: Stream Int
badAfterDestructor =
  stailS (0 :> badAfterDestructor)

--------------------------------------------------------------------------------
-- 7. Branch-dependent productivity with delayed streams (filterS)
--
-- Sources:
--   Danielsson (2010), Beating the Productivity Checker Using Embedded
--   Languages, Section 2.
--
-- EXPECTED: REJECT (NOT PRODUCTIVE FOR ALL INPUTS).
--
-- filterS emits a constructor in the true branch, but recurses through
-- forceLater without emitting a constructor in the otherwise branch. On an
-- infinite stream where p is always False, no output constructor is produced.
--------------------------------------------------------------------------------

{-@ lazy repeatDS @-}
repeatDS :: a -> DelayedStream a
repeatDS x = DSCons x (Later (repeatDS x))

filterS :: (a -> Bool) -> DelayedStream a -> DelayedStream a
filterS _ DSNil = DSNil
filterS p (DSCons x xs)
  | p x       = DSCons x (Later (filterS p (forceLater xs)))
  | otherwise = filterS p (forceLater xs)

filterNoMatches :: DelayedStream Int
filterNoMatches = filterS (\_ -> False) (repeatDS 0)

--------------------------------------------------------------------------------
-- 8. Nested inductive/coinductive guard leakage (Tree / CoList)
--
-- Sources:
--   Altenkirch and Danielsson (2010), Termination Checking in the Presence of
--   Nested Inductive and Coinductive Types.
--
-- EXPECTED: REJECT (NON-TOTAL / GUARD LEAKAGE).
--
-- The delay constructors belong to the inner coinductive CoList, but a naive
-- checker lets them guard recursion through the outer inductive Tree.
--------------------------------------------------------------------------------

data CoList a
  = CoNil
  | CoCons a (Later (CoList a))

data Tree = TreeNode (CoList Tree)

badTree :: Tree
badTree = TreeNode (CoCons (TreeNode CoNil) (Later badTrees))

badTrees :: CoList Tree
badTrees = CoCons badTree (Later badTrees)

--------------------------------------------------------------------------------
-- 9. Nested inductive/coinductive guard leakage (STree / DelayedStream)
--
-- Sources:
--   Hyvernat (2022), The Size-Change Principle for Mixed Inductive and
--   Coinductive Types, Section 2.
--
-- EXPECTED: REJECT (NON-TOTAL / INHABITS FALSE).
--
-- STree is inductive while DelayedStream is coinductive. badS is productive
-- as a stream, but its head contains an infinitely deep STree, allowing
-- lowerLeft and magicFalse to inhabit FalseProof.
--------------------------------------------------------------------------------

data STree = STNode (DelayedStream STree) | STNil

{-@ measure isSTNode @-}
isSTNode :: STree -> Bool
isSTNode (STNode _) = True
isSTNode STNil      = False

{-@ type ISTree = {v:STree | isSTNode v} @-}
{-@ data STree = STNode (IDelayedStream ISTree) | STNil @-}

{-@ dstreamHead :: IDelayedStream a -> a @-}
dstreamHead :: DelayedStream a -> a
dstreamHead (DSCons x _) = x

{-@ badS :: IDelayedStream ISTree @-}
badS :: DelayedStream STree
badS = DSCons (STNode badS) (Later badS)

{-@ lowerLeft :: ISTree -> a @-}
lowerLeft :: STree -> a
lowerLeft (STNode s) = lowerLeft (dstreamHead s)

magic :: a
magic = lowerLeft (dstreamHead badS)

{-@ magicFalse :: FalseProof @-}
magicFalse :: ()
magicFalse = lowerLeft (dstreamHead badS)

--------------------------------------------------------------------------------
-- 10. Higher-order codata field: stream processor sink
--
-- Sources:
--   Danielsson (2010), Beating the Productivity Checker Using Embedded
--   Languages, Section 2.
--
-- EXPECTED: REJECT (NON-PRODUCTIVE / UNDELAYED GET).
--
-- The recursive continuation of Put is delayed, while Get is not. Infinitely
-- many consecutive Gets without a Put are non-productive.
--------------------------------------------------------------------------------

data StreamProcessor a b
  = Put b (Later (StreamProcessor a b))
  | Get (a -> StreamProcessor a b)
  | SPNil

sink :: StreamProcessor a b
sink = Get (\_ -> sink)

--------------------------------------------------------------------------------
-- 11. Unguarded mutual recursion cycle
--
-- Sources:
--   Liquid Haskell PR #2771 (recursive CAF handling).
--
-- EXPECTED: REJECT (UNGUARDED RECURSIVE CYCLE).
--
-- Neither mutualA nor mutualB produces a constructor; the mutual dependency
-- cycle makes no observable progress.
--------------------------------------------------------------------------------

mutualA :: Stream Int
mutualA = mutualB

mutualB :: Stream Int
mutualB = mutualA

--------------------------------------------------------------------------------
-- 12. Strict recursive codata field
--
-- Sources:
--   Haskell strict data constructor semantics.
--
-- EXPECTED: REJECT (NON-PRODUCTIVE STRICT RECURSION).
--
-- Strictness on the recursive field forces evaluation before StrictCons can
-- be exposed, causing strictBad to diverge immediately.
--------------------------------------------------------------------------------

data StrictStream a
  = StrictCons a !(StrictStream a)
  | StrictNil

strictBad :: StrictStream Int
strictBad = StrictCons 0 strictBad

--------------------------------------------------------------------------------
-- 13. Non-executable Dafny reference cases (co-friendliness & least fixpoint)
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figures 14 and 15.
--
-- EXPECTED: REJECT (CO-FRIENDLINESS / TERMINATION RESTRICTION IN DAFNY).
--
-- Preserved as reference specifications for future copredicate checks:
--   * NotAll' (Fig. 14): recursive call under unbounded existential quantifier.
--   * InfOften'' (Fig. 14): recursive call under unbounded existential quantifier.
--   * IsFinite_LeastFixpoint (Fig. 15): recursive traversal of infinite stream
--     without a well-founded termination argument.
--------------------------------------------------------------------------------
