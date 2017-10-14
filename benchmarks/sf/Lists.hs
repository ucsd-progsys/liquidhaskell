{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Lists where

import qualified Prelude
import           Prelude (Char, Int, Bool (..))
import Language.Haskell.Liquid.ProofCombinators

-- TODO: import Basics and Induction

{-@ safeEq :: x : a -> { y : a | x = y } -> a @-}
safeEq :: a -> a -> a
safeEq x y = y

{-@ since :: x : a -> reason : b -> a @-}
since :: a -> b -> a
since x reason = x

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

{-@ reflect mult @-}
mult :: Peano -> Peano -> Peano
mult n m = case n of
  O    -> O
  S n' -> plus m (mult n' m)

{-@ reflect p0 @-}
p0 = O
{-@ reflect p1 @-}
p1 = S p0
{-@ reflect p2 @-}
p2 = S p1
{-@ reflect p3 @-}
p3 = S p2
{-@ reflect p4 @-}
p4 = S p3
{-@ reflect p5 @-}
p5 = S p4
{-@ reflect p6 @-}
p6 = S p5
{-@ reflect p7 @-}
p7 = S p6
{-@ reflect p8 @-}
p8 = S p7
{-@ reflect p9 @-}
p9 = S p8

{-@ data BBool = BTrue | BFalse @-}
data BBool = BTrue | BFalse

{-@ reflect andb @-}
andb :: BBool -> BBool -> BBool
andb BTrue BTrue = BTrue
andb _     _     = BFalse

{-@ reflect negb @-}
negb :: BBool -> BBool
negb BTrue  = BFalse
negb BFalse = BTrue

{-@ reflect evenb @-}
evenb :: Peano -> BBool
evenb O         = BTrue
evenb (S O)     = BFalse
evenb (S (S n)) = evenb n

{-@ reflect beq @-}
beq :: Peano -> Peano -> BBool
beq O     O     = BTrue
beq (S m) (S n) = beq m n
beq _     _     = BFalse

{-@ reflect ble @-}
ble :: Peano -> Peano -> BBool
ble O     _     = BTrue
ble (S m) O     = BFalse
ble (S m) (S n) = ble m n

--------------------------------------------------------------------------------
-- | Pairs of Numbers ----------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data PeanoProd = Pair { fstp :: Peano, sndp :: Peano } @-}
data PeanoProd = Pair { fstp :: Peano, sndp :: Peano }

{-@ reflect swap @-}
swap :: PeanoProd -> PeanoProd
swap (Pair x y) = Pair y x

{-@
  thmSurjectiveProding :: p : PeanoProd -> { p = Pair (fstp p) (sndp p) }
@-}
thmSurjectiveProding :: PeanoProd -> Proof
thmSurjectiveProding p@(Pair x y) = ( fstp p, sndp p ) *** QED

--------------------------------------------------------------------------------
-- | Exercise : fst, snd, swap -------------------------------------------------
--------------------------------------------------------------------------------

{-@
  thmSndFstIsSwap :: p : PeanoProd -> { (swap p) = Pair (sndp p) (fstp p) }
@-}
thmSndFstIsSwap :: PeanoProd -> Proof
thmSndFstIsSwap p@(Pair x y) = ( swap p, fstp p, sndp p ) *** QED

{-@
  thmFstSwapIsSnd :: p : PeanoProd -> { (fstp (swap p)) = (sndp p) }
@-}
thmFstSwapIsSnd :: PeanoProd -> Proof
thmFstSwapIsSnd p@(Pair x y) = ( fstp (swap p), sndp p ) *** QED

--------------------------------------------------------------------------------
-- | Lists of Numbers ----------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data NatList [nlen] = Nil | Cons (nhd :: Peano) (ntl :: NatList) @-}
data NatList = Nil | Cons Peano NatList

{-@ measure nlen @-}
{-@ nlen :: NatList -> Nat @-}
nlen :: NatList -> Int
nlen Nil        = 0
nlen (Cons _ t) = 1 Prelude.+ nlen t

{-@ reflect length @-}
length :: NatList -> Peano
length Nil        = O
length (Cons h t) = S (length t)

{-@ reflect app @-}
app :: NatList -> NatList -> NatList
app Nil        l2 = l2
app (Cons h t) l2 = Cons h (app t l2)

{-@ reflect hd @-}
hd :: Peano -> NatList -> Peano
hd def Nil        = def
hd _   (Cons h t) = h

{-@ reflect tl @-}
tl :: NatList -> NatList
tl Nil        = Nil
tl (Cons h t) = t

--------------------------------------------------------------------------------
-- | Exercise : list_funs ------------------------------------------------------
--------------------------------------------------------------------------------

{-@ reflect filter @-}
filter :: (Peano -> BBool) -> NatList  -> NatList
filter pred Nil        = Nil
filter pred (Cons h t) = case pred h of
  BTrue  -> Cons h (filter pred t)
  BFalse -> filter pred t

-- TODO: LH fails to compile curried code and reports sort error:
-- nonzeros = filter (\x -> negb (beq x O))

{-@ reflect nonzeros @-}
nonzeros' :: NatList -> NatList
nonzeros' l = filter (\x -> negb (beq x O)) l

-- TODO: Stuck. See: https://github.com/ucsd-progsys/liquidhaskell/issues/1035

-- {-@ testNonzeros' :: {
--   nonzeros' (Cons p0 (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil))))))) =
--   (Cons p1 (Cons p2 (Cons p3 Nil))) } @-}

-- -- testNonzeros' = trivial

-- testNonzeros'
--   =   nonzeros (Cons p0 (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil)))))))
--   ==. filter (\x -> negb (beq x O)) (Cons p0 (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil)))))))
--   ==. filter (\x -> negb (beq x O)) (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil))))))
--   ==. Cons p1 (filter (\x -> negb (beq x O)) (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil))))))
--   ==. Cons p1 (filter (\x -> negb (beq x O)) (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil)))))
--   ==. Cons p1 (Cons p2 (filter (\x -> negb (beq x O)) (Cons p3 (Cons p0 (Cons p0 Nil)))))
--   ==. Cons p1 (Cons p2 (Cons p3 (filter (\x -> negb (beq x O)) (Cons p0 (Cons p0 Nil)))))
--   ==. Cons p1 (Cons p2 (Cons p3 (filter (\x -> negb (beq x O)) (Cons p0 Nil))))
--   ==. Cons p1 (Cons p2 (Cons p3 (filter (\x -> negb (beq x O)) Nil)))
--   ==. Cons p1 (Cons p2 (Cons p3 Nil))
--   *** QED

{-@ reflect nonzeros @-}
nonzeros :: NatList -> NatList
nonzeros Nil        = Nil
nonzeros (Cons O t) = nonzeros t
nonzeros (Cons h t) = Cons h (nonzeros t)

-- {-@ testNonzeros :: {
--   nonzeros (Cons p0 (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil))))))) =
--   (Cons p1 (Cons p2 (Cons p3 Nil))) } @-}
-- testNonzeros = trivial

{-@ reflect oddmembers @-}
oddmembers :: NatList -> NatList
oddmembers Nil        = Nil
oddmembers (Cons h t) = case evenb h of
  BTrue  -> oddmembers t
  BFalse -> Cons h (oddmembers t)

-- {-@ testOddmembers :: {
--   oddmembers (Cons p0 (Cons p1 (Cons p0 (Cons p2 (Cons p3 (Cons p0 (Cons p0 Nil))))))) =
--   (Cons p1 (Cons p3 Nil)) } @-}
-- testOddmembers = trivial

{-@ reflect countOddmembers @-}
countOddmembers :: NatList -> Peano
countOddmembers l = length (oddmembers l)

-- {-@ testCountOddmembers1 :: {
--   countOddmembers (Cons p1 (Cons p0 (Cons p3 (Cons p1 (Cons p4 (Cons p5 Nil)))))) =
--   p4 } @-}
-- testCountOddmembers1 = trivial

-- {-@ testCountOddmembers2 :: {
--  countOddmembers (Cons p0 (Cons p2 (Cons p4 Nil))) = p0 } @-}
-- testCountOddmembers2 = trivial

-- {-@ testCountOddmembers3 :: {
--   countOddmembers Nil = p0 } @-}
-- testCountOddmembers3 = trivial

--------------------------------------------------------------------------------
-- | Exercise : alternate ------------------------------------------------------
--------------------------------------------------------------------------------

-- {-@ reflect alternate @-}
-- alternate :: NatList -> NatList -> NatList
-- alternate Nil          l2           = l2
-- alternate l1           Nil          = l1
-- alternate (Cons h1 t1) (Cons h2 t2) = Cons h1 (Cons h2 (alternate t1 t2))

-- {-@ testAlternate1 :: {
--   alternate (Cons p1 (Cons p2 (Cons p3 Nil))) (Cons p4 (Cons p5 (Cons p6 Nil))) =
--   (Cons p1 (Cons p4 (Cons p2 (Cons p5 (Cons p3 (Cons p6 Nil)))))) } @-}
-- testAlternate1 = trivial

-- {-@ testAlternate2 :: {
--   alternate (Cons p1 Nil) (Cons p4 (Cons p5 (Cons p6 Nil))) =
--   (Cons p1 (Cons p4 (Cons p5 (Cons p6 Nil)))) } @-}
-- testAlternate2 = trivial

-- {-@ testAlternate3 :: {
--   alternate (Cons p1 (Cons p2 (Cons p3 Nil))) (Cons p4 Nil) =
--   (Cons p1 (Cons p4 (Cons p2 (Cons p3 Nil)))) } @-}
-- testAlternate3 = trivial

-- {-@ testAlternate4 :: {
--   alternate Nil (Cons p8 (Cons p9 Nil)) =
--   (Cons p8 (Cons p9 Nil)) } @-}
-- testAlternate4 = trivial

--------------------------------------------------------------------------------
-- | Exercise : bag_functions --------------------------------------------------
--------------------------------------------------------------------------------

{-@ type Bag = NatList @-}
type Bag = NatList

{-@ reflect count @-}
{-@ count :: Peano -> bag : Bag -> Peano / [nlen bag] @-}
count :: Peano -> Bag -> Peano
count _ Nil        = O
count v (Cons h t) = case beq v h of
  BTrue  -> S (count v t)
  BFalse -> count v t

-- {-@ testCount1 :: {
--   count p1 (Cons p1 (Cons p2 (Cons p3 (Cons p1 (Cons p4 (Cons p1 Nil)))))) = p3
--   } @-}
-- testCount1 = trivial

-- {-@ testCount2 :: {
--   count p6 (Cons p1 (Cons p2 (Cons p3 (Cons p1 (Cons p4 (Cons p1 Nil)))))) = p0
--   } @-}
-- testCount2 = trivial

{-@ reflect sum @-}
sum l1 l2 = app l1 l2

-- {-@ testSum :: {
--   count p1 (sum (Cons p1 (Cons p2 (Cons p3 Nil))) (Cons p1 (Cons p4 (Cons p1 Nil)))) =
--   p3 } @-}
-- testSum = trivial

{-@ reflect add @-}
add v s = Cons v s

-- {-@ testAdd1 :: {
--   count p1 (add p1 (Cons p1 (Cons p4 (Cons p1 Nil)))) = p3 } @-}
-- testAdd1 = trivial

-- {-@ testAdd2 :: {
--   count p5 (add p1 (Cons p1 (Cons p4 (Cons p1 Nil)))) = p0 } @-}
-- testAdd2 = trivial

{-@ reflect member @-}
member :: Peano -> Bag -> BBool
member v s = negb (beq (count v s) O)

-- {-@ testMember1 :: {
--   member p1 (Cons p1 (Cons p4 (Cons p1 Nil))) = BTrue } @-}
-- testMember1 = trivial

-- {-@ testMember2 :: {
--   member p2 (Cons p1 (Cons p4 (Cons p1 Nil))) = BFalse } @-}
-- testMember2 = trivial

--------------------------------------------------------------------------------
-- | Exercise : bag_more_functions ---------------------------------------------
--------------------------------------------------------------------------------

{-@ reflect removeOne @-}
{-@ removeOne :: Peano -> bag : Bag -> Bag / [nlen bag] @-}
removeOne :: Peano -> Bag -> Bag
removeOne _ Nil        = Nil
removeOne v (Cons h t) = case beq v h of
  BTrue  -> t
  BFalse -> Cons h (removeOne v t)

-- {-@ testRemoveOne1 :: {
--   count p5 (removeOne p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p1 Nil)))))) =
--   p0 } @-}
-- testRemoveOne1 = trivial

-- {-@ testRemoveOne2 :: {
--   count p5 (removeOne p5 (Cons p2 (Cons p1 (Cons p4 (Cons p1 Nil))))) =
--   p0 } @-}
-- testRemoveOne2 = trivial

-- {-@ testRemoveOne3 :: {
--   count p4 (removeOne p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p1 (Cons p4 Nil))))))) =
--   p2 } @-}
-- testRemoveOne3 = trivial

-- {-@ testRemoveOne4 :: {
--   count p5 (removeOne p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p5 (Cons p1 (Cons p4 Nil)))))))) =
--   p1 } @-}
-- testRemoveOne4 = trivial

{-@ reflect removeAll @-}
{-@ removeAll :: Peano -> bag : Bag -> Bag / [nlen bag] @-}
removeAll :: Peano -> Bag -> Bag
removeAll _ Nil        = Nil
removeAll v (Cons h t) = case beq v h of
  BTrue  -> removeAll v t
  BFalse -> Cons h (removeAll v t)

-- {-@ testRemoveAll1 :: {
--   count p5 (removeAll p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p1 Nil)))))) =
--   p0 } @-}
-- testRemoveAll1 = trivial

-- {-@ testRemoveAll2 :: {
--   count p5 (removeAll p5 (Cons p2 (Cons p1 (Cons p4 (Cons p1 Nil))))) =
--   p0 } @-}
-- testRemoveAll2 = trivial

-- {-@ testRemoveAll3 :: {
--   count p4 (removeAll p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p1 (Cons p4 Nil))))))) =
--   p2 } @-}
-- testRemoveAll3 = trivial

-- {-@ testRemoveAll4 :: {
--   count p5 (removeAll p5 (Cons p2 (Cons p1 (Cons p5 (Cons p4 (Cons p5 (Cons p1 (Cons p4 Nil)))))))) =
--   p0 } @-}
-- testRemoveAll4 = trivial

{-@ reflect subset @-}
subset :: Bag -> Bag -> BBool
subset Nil        _  = BTrue
subset (Cons h t) s2 = case member h s2 of
  BTrue  -> subset t (removeOne h s2)
  BFalse -> BFalse

-- {-@ testSubset1 :: {
--   (subset (Cons p1 (Cons p2 Nil)) (Cons p2 (Cons p1 (Cons p4 (Cons p1 Nil))))) =
--   BTrue } @-}
-- testSubset1 = trivial

-- {-@ testSubset2 :: {
--   (subset (Cons p1 (Cons p2 (Cons p2 Nil))) (Cons p2 (Cons p1 (Cons p4 (Cons p1 Nil))))) =
--   BFalse } @-}
-- testSubset2 = trivial

--------------------------------------------------------------------------------
-- | Exercise : bag_theorem ----------------------------------------------------
--------------------------------------------------------------------------------

-- SF asks to write down a theorem about count and add. I write down one
-- about member and removeOne, which I think is more interesting.
-- However, it is blocked by the issue
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1036

-- {-@ thmBag :: v : Peano
--            -> { s : Bag | (member v s) = BTrue }
--            -> { length s = S (length (removeOne v s)) }
--            / [nlen s]
--  @-}
-- thmBag :: Peano -> Bag -> Proof
-- thmBag v s@Nil        = trivial
-- thmBag v s@(Cons h t) = case beq v h of
--   BTrue  -> trivial
--   BFalse -> length s
--    `safeEq` S (length t)
--    `safeEq` S (S (length (removeOne v t)))
--     `since` (member v t `safeEq` BTrue, thmBag v t)
--    `safeEq` S (length (removeOne v s))
--         *** QED

--------------------------------------------------------------------------------
-- | Reasoning About Lists -----------------------------------------------------
--------------------------------------------------------------------------------

{-@ thmNilApp :: { lhs : NatList | lhs = Nil }
              -> rhs : NatList
              -> { app lhs rhs = rhs }
@-}
thmNilApp :: NatList -> NatList -> Proof
thmNilApp Nil rhs = trivial
thmNilApp _   _   = trivial -- impossible

{-@ reflect pred @-}
pred :: Peano -> Peano
pred O     = O
pred (S n) = n

{-@ thmTlLengthPred :: l : NatList
                    -> { pred (length l) = length (tl l) }
@-}
thmTlLengthPred :: NatList -> Proof
thmTlLengthPred Nil        = trivial
thmTlLengthPred (Cons h t) = trivial

{-@ thmAppAssoc :: l1 : NatList -> l2 : NatList -> l3 : NatList
                -> { app (app l1 l2) l3 = app l1 (app l2 l3) }
@-}
thmAppAssoc :: NatList -> NatList -> NatList -> Proof
thmAppAssoc Nil          _  _  = trivial
thmAppAssoc (Cons n l1') l2 l3 = (thmAppAssoc l1' l2 l3) *** QED

--------------------------------------------------------------------------------
-- | Reversing A List ----------------------------------------------------------
--------------------------------------------------------------------------------

{-@ reflect reverse @-}
reverse :: NatList -> NatList
reverse Nil        = Nil
reverse (Cons h t) = app (reverse t) (Cons h Nil)

-- {-@ testReverse1 :: { reverse (Cons p1 (Cons p2 (Cons p3 Nil))) =
--   (Cons p3 (Cons p2 (Cons p1 Nil))) } @-}
-- testReverse1 = trivial

-- {-@ testReverse2 :: { reverse Nil = Nil } @-}
-- testReverse2 = trivial

{-@ thmAppLength :: l1 : NatList
                 -> l2 : NatList
                 -> { length (app l1 l2) = plus (length l1) (length l2) }
@-}
thmAppLength :: NatList -> NatList -> Proof
thmAppLength Nil          _  = trivial
thmAppLength (Cons h1 t1) l2 = (thmAppLength t1 l2) *** QED

{-@ thmPlusComm :: n : Peano -> m : Peano
                -> { plus n m = plus m n }
@-}
thmPlusComm :: Peano -> Peano -> Proof
thmPlusComm O      m = plus O m
              `safeEq` m
              `safeEq` (plus m O `since` lemPlusNO m)
                  ***  QED
thmPlusComm (S n') m = plus (S n') m
              `safeEq` S (plus n' m)
              `safeEq` (S (plus m n') `since` thmPlusComm n' m)
              `safeEq` (plus m (S n') `since` lemPlusNSm m n')
                  ***  QED

{-@ lemPlusNO :: n : Peano -> { n = plus n O } @-}
lemPlusNO :: Peano -> Proof
lemPlusNO O     = trivial
lemPlusNO (S n) = S n `safeEq` (S (plus n O) `since` lemPlusNO n) ***QED

{-@ lemPlusNSm :: n : Peano -> m : Peano
               -> { S (plus n m) = plus n (S m) }
@-}
lemPlusNSm :: Peano -> Peano -> Proof
lemPlusNSm O     m = trivial
lemPlusNSm (S n) m = S (plus (S n) m)
            `safeEq` S (S (plus n m))
            `safeEq` (S (plus n (S m)) `since` lemPlusNSm n m)
            `safeEq` plus (S n) (S m)
                ***  QED

{-@ thmRevLength :: l : NatList
                 -> { length (reverse l) = length l }
@-}
thmRevLength Nil        = trivial
thmRevLength (Cons h t) = length (reverse (Cons h t))
                 `safeEq` length (app (reverse t) (Cons h Nil))
                 `safeEq` (plus (length (reverse t)) (length (Cons h Nil))
                  `since` thmAppLength (reverse t) (Cons h Nil))
                 `safeEq` (plus (length t) (length (Cons h Nil))
                  `since` thmRevLength t)
                 `safeEq` plus (length t) (S O)
                 `safeEq` (plus (S O) (length t)
                  `since` thmPlusComm (length t) (S O))
                 `safeEq` S (length t)
                 `safeEq` length (Cons h t)
                     ***  QED

--------------------------------------------------------------------------------
-- | List Exercises, Part 1 ----------------------------------------------------
--------------------------------------------------------------------------------

{-@ thmAppNilR :: l : NatList -> { app l Nil = l } @-}
thmAppNilR :: NatList -> Proof
thmAppNilR Nil        = trivial
thmAppNilR (Cons h t) = app (Cons h t) Nil
               `safeEq` Cons h (app t Nil)
               `safeEq` (Cons h t `since` thmAppNilR t)
                   ***  QED

{-@ thmRevAppDistr :: l1 : NatList -> l2 : NatList
                   -> { reverse (app l1 l2) = app (reverse l2) (reverse l1) }
@-}
thmRevAppDistr :: NatList -> NatList -> Proof
thmRevAppDistr Nil          l2 =
  reverse (app Nil l2)          `safeEq`
  reverse l2                    `safeEq`
  (app (reverse l2) Nil         `since`
    thmAppNilR (reverse l2))    `safeEq`
  app (reverse l2) (reverse Nil) *** QED

thmRevAppDistr (Cons h1 t1) l2 =
  reverse (app (Cons h1 t1) l2)           `safeEq`
  reverse (Cons h1 (app t1 l2))           `safeEq`
  app (reverse (app t1 l2)) (Cons h1 Nil) `safeEq`
  (app (app (reverse l2) (reverse t1))
       (Cons h1 Nil)                      `since`
    thmRevAppDistr t1 l2)                 `safeEq`
  (app (reverse l2)
      (app (reverse t1) (Cons h1 Nil))    `since`
    thmAppAssoc (reverse l2)
                (reverse t1)
                (Cons h1 Nil))            `safeEq`
  app (reverse l2) (reverse (Cons h1 t1))  *** QED

{-@ thmRevInvolutive :: l : NatList
                     -> { reverse (reverse l) = l }
@-}
thmRevInvolutive :: NatList -> Proof
thmRevInvolutive Nil        = trivial
thmRevInvolutive (Cons h t) = reverse (reverse (Cons h t))
                     `safeEq` reverse (app (reverse t) (Cons h Nil))
                     `safeEq` (app (reverse (Cons h Nil)) (reverse (reverse t))
                      `since` thmRevAppDistr (reverse t) (Cons h Nil))
                     `safeEq` app (Cons h Nil) (reverse (reverse t))
                     `safeEq` (app (Cons h Nil) t
                      `since` thmRevInvolutive t)
                     `safeEq` (Cons h t)
                         ***  QED

{-@ thmAppAssoc4 :: l1 : NatList -> l2 : NatList -> l3 : NatList -> l4 : NatList
                 -> { (app l1 (app l2 (app l3 l4))) =
                      (app (app (app l1 l2) l3) l4) }
@-}
thmAppAssoc4 :: NatList -> NatList -> NatList -> NatList -> Proof
thmAppAssoc4 Nil          l2 l3 l4 = app Nil (app l2 (app l3 l4))
                            `safeEq` app l2 (app l3 l4)
                            `safeEq` (app (app l2 l3) l4
                             `since` thmAppAssoc l2 l3 l4)
                            `safeEq` app (app (app Nil l2) l3) l4
                                ***  QED
thmAppAssoc4 (Cons h1 t1) l2 l3 l4 = app (Cons h1 t1) (app l2 (app l3 l4))
                            `safeEq` Cons h1 (app t1 (app l2 (app l3 l4)))
                            `safeEq` (Cons h1 (app (app (app t1 l2) l3) l4)
                             `since` thmAppAssoc4 t1 l2 l3 l4)
                            `safeEq` app (Cons h1 (app (app t1 l2) l3)) l4
                            `safeEq` app (app (Cons h1 (app t1 l2)) l3) l4
                            `safeEq` app (app (app (Cons h1 t1) l2) l3) l4
                                ***  QED

{-@ thmNonZerosApp :: l1 : NatList -> l2 : NatList
                   -> { nonzeros (app l1 l2) = app (nonzeros l1) (nonzeros l2) }
@-}
thmNonZerosApp Nil             l2 = trivial
thmNonZerosApp (Cons O     t1) l2 = nonzeros (app (Cons O t1) l2)
                           `safeEq` nonzeros (Cons O (app t1 l2))
                           `safeEq` nonzeros (app t1 l2)
                           `safeEq` (app (nonzeros t1) (nonzeros l2)
                            `since` thmNonZerosApp t1 l2)
                           `safeEq` app (nonzeros (Cons O t1)) (nonzeros l2)
                               ***  QED
thmNonZerosApp (Cons (S x) t1) l2 = nonzeros (app (Cons (S x) t1) l2)
                           `safeEq` nonzeros (Cons (S x) (app t1 l2))
                           `safeEq` Cons (S x) (nonzeros (app t1 l2))
                           `safeEq` (Cons (S x)
                                          (app (nonzeros t1) (nonzeros l2))
                            `since` thmNonZerosApp t1  l2)
                           `safeEq` app (Cons (S x) (nonzeros t1)) (nonzeros l2)
                           `safeEq` app (nonzeros (Cons (S x) t1)) (nonzeros l2)
                               ***  QED

{-@ reflect beqNatList @-}
beqNatList :: NatList -> NatList -> BBool
beqNatList Nil          Nil          = BTrue
beqNatList Nil          _            = BFalse
beqNatList _            Nil          = BFalse
beqNatList (Cons h1 t1) (Cons h2 t2) = andb (beq h1 h2) (beqNatList t1 t2)

{-@ lemBeqRefl :: x : Peano -> { beq x x = BTrue } @-}
lemBeqRefl :: Peano -> Proof
lemBeqRefl O     = trivial
lemBeqRefl (S x) = beq (S x) (S x)
                `safeEq` beq x x
                `safeEq` (BTrue `since` lemBeqRefl x)
                    ***  QED

{-@ thmBeqNatListRefl :: l : NatList
                      -> { beqNatList l l = BTrue }
@-}
thmBeqNatListRefl :: NatList -> Proof
thmBeqNatListRefl Nil          = trivial
thmBeqNatListRefl (Cons h1 t1) =
  beqNatList (Cons h1 t1) (Cons h1 t1) `safeEq`
  andb (beq h1 h1) (beqNatList t1 t1)  `safeEq`
  (andb (beq h1 h1) BTrue              `since`
    thmBeqNatListRefl t1)              `safeEq`
  (andb BTrue BTrue                    `since`
    lemBeqRefl h1)                     `safeEq`
  BTrue                                 *** QED

--------------------------------------------------------------------------------
-- | List Exercises, Part 2 ----------------------------------------------------
--------------------------------------------------------------------------------

-- Also blocked by https://github.com/ucsd-progsys/liquidhaskell/issues/1036

-- {-@ thmRevInjective :: l1 : NatList
--                     -> l2 : { NatList | reverse l1 = reverse l2 }
--                     -> { l1 = l2 }
-- @-}
-- thmRevInjective l1 l2 = l1
--                `safeEq` (reverse (reverse l1) `since` thmRevInvolutive l1)
--                `safeEq` reverse (reverse l2)
--                `safeEq` (l2 `since` thmRevInvolutive l2)
--                    ***  QED

--------------------------------------------------------------------------------
-- | Options -------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data NatOption = None | Some (natOptionPayload :: Peano)@-}
data NatOption = None | Some Peano

{-@ reflect nthError @-}
nthError :: NatList -> Peano -> NatOption
nthError Nil        _     = None
nthError (Cons h _) O     = Some h
nthError (Cons _ t) (S n) = nthError t n

-- {-@
--   testNthError1 :: { nthError (Cons p4 (Cons p5 (Cons p6 (Cons p7 Nil)))) p0 = Some p4 }
-- @-}
-- testNthError1 = trivial

-- {-@
--   testNthError2 :: { nthError (Cons p4 (Cons p5 (Cons p6 (Cons p7 Nil)))) p3 = Some p7 }
-- @-}
-- testNthError2 = trivial

-- {-@
--   testNthError3 :: { nthError (Cons p4 (Cons p5 (Cons p6 (Cons p7 Nil)))) p9 = None }
-- @-}
-- testNthError3 = trivial

{-@ reflect optionElim @-}
optionElim :: Peano -> NatOption -> Peano
optionElim d None     = d
optionElim _ (Some x) = x

{-@ reflect hdError @-}
hdError :: NatList -> NatOption
hdError Nil        = None
hdError (Cons h _) = Some h

-- {-@
--   testHdError1 :: { hdError Nil = None }
-- @-}
-- testHdError1 = trivial

-- {-@
--   testHdError2 :: { hdError Nil = None }
-- @-}
-- testHdError2 = trivial

-- {-@
--   testHdError3 :: { hdError Nil = None }
-- @-}
-- testHdError3 = trivial

-- Simple induction can be solved by LH trivially.
{-@
  thmOptionElimHd :: l : NatList
                  -> def : Peano
                  -> { hd def l = optionElim def (hdError l) }
@-}
thmOptionElimHd :: NatList -> Peano -> Proof
thmOptionElimHd l def = trivial

--------------------------------------------------------------------------------
-- | Partial Maps --------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Id = Id { unId :: Peano } @-}
data Id = Id Peano

{-@ reflect beqId @-}
beqId :: Id -> Id -> BBool
beqId (Id x) (Id y) = beq x y

{-@
  thmEqBeq :: m : Peano -> n : { Peano | m = n } -> { beq m n = BTrue }
@-}
thmEqBeq :: Peano -> Peano -> Proof
thmEqBeq O O         = trivial
thmEqBeq (S m) (S n) = thmEqBeq m n

{-@
  thmBeqIdRefl :: x : Id -> { beqId x x = BTrue }
@-}
thmBeqIdRefl :: Id -> Proof
thmBeqIdRefl x'@(Id x) = beqId x' x'
                `safeEq` beq x x
                `safeEq` (BTrue `since` thmEqBeq x x)
                     *** QED

{-@
  data PartialMap [nlen'] = Empty
    | Record (getKey :: Id) (getVal :: Peano) (getRest :: PartialMap)
@-}
data PartialMap = Empty | Record Id Peano PartialMap

{-@ measure nlen' @-}
{-@ nlen' :: PartialMap -> Nat @-}
nlen' :: PartialMap -> Int
nlen' Empty          = 0
nlen' (Record _ _ t) = 1 Prelude.+ nlen' t

{-@ reflect update @-}
update :: PartialMap -> Id -> Peano -> PartialMap
update old key val = Record key val old

{-@ reflect find @-}
find :: Id -> PartialMap -> NatOption
find _ Empty          = None
find x (Record y v t) = case beqId x y of
  BTrue  -> Some v
  BFalse -> find x t

{-@
  thmUpdateEq :: map : PartialMap -> key : Id -> val : Peano
              -> { find key (update map key val) = Some val }
@-}
thmUpdateEq :: PartialMap -> Id -> Peano -> Proof
thmUpdateEq map key val = find key (update map key val)
                 `safeEq` find key (Record key val map)
                 `safeEq` (Some val `since` thmBeqIdRefl key)
                      *** QED

{-@
  thmUpdateNeq :: map : PartialMap
               -> x : Id -> y : { Id | beqId y x = BFalse }
               -> val : Peano
               -> { find y (update map x val) = find y map }
@-}
thmUpdateNeq :: PartialMap -> Id -> Id -> Peano -> Proof
thmUpdateNeq map x y val = find y (update map x val)
                  `safeEq` find y (Record x val map)
                  `safeEq` (find y map `since` beqId y x)
                      *** QED
