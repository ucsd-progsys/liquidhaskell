{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{- NOTE:

   1. See the TODO:trivial for cases where the instances seems to fail

   2. Would be nice to have case-splitting combinatores,
      e.g. for thmAndbCom,  thmAndbExch which are super boilerplate-y

   3. For @minsheng: See the rewritten signature for `thmEqBeq`;
      we don't really need `rewrite` as the SMT
      does "congruence closure" automatically.

 -}

module Basics where

  -- (
    -- -- * Booleans
    -- Bool(..)
  -- , negb, andb, orb
--
    -- -- * Peano numerals
  -- , Peano(..), toNat
  -- , plus, mult
  -- , beq, ble, blt
  -- )
  -- where

import           Prelude (Char, Int)
import qualified Prelude
import           Language.Haskell.Liquid.ProofCombinators

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x Prelude.+ 1


--------------------------------------------------------------------------------
-- | Days ----------------------------------------------------------------------
--------------------------------------------------------------------------------

-- NOTE: clunky to have to redefine this ...

{-@ data Day = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday
  @-}

data Day = Monday
         | Tuesday
         | Wednesday
         | Thursday
         | Friday
         | Saturday
         | Sunday

{-@ reflect nextWeekDay @-}
nextWeekDay :: Day -> Day
nextWeekDay Monday    = Tuesday
nextWeekDay Tuesday   = Wednesday
nextWeekDay Wednesday = Thursday
nextWeekDay Thursday  = Friday
nextWeekDay Friday    = Monday
nextWeekDay Saturday  = Monday
nextWeekDay Sunday    = Monday


{-@ testNextWeekDay :: { nextWeekDay (nextWeekDay Saturday) == Tuesday } @-}
testNextWeekDay
  = trivial

--------------------------------------------------------------------------------
-- | Booleans ------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Bool = True | False @-}
data Bool = True | False

{-@ reflect negb @-}
negb :: Bool -> Bool
negb True  = False
negb False = True

{-@ reflect orb @-}
orb :: Bool -> Bool -> Bool
orb False False = False
orb _     _     = True

{-@ testOr1 :: { orb True True == True } @-}
testOr1 = trivial

{-@ testOr2 :: { orb True False == True } @-}
testOr2 = trivial

{-@ testOr3 :: { orb False True == True } @-}
testOr3 = trivial

{-@ testOr4 :: { orb False False == False } @-}
testOr4 = trivial

{-@ reflect andb @-}
andb :: Bool -> Bool -> Bool
andb True True = True
andb _    _    = False

{-@ andbCom :: a:_ -> b:_ -> { andb a b = andb b a } @-}
andbCom :: Bool -> Bool -> Proof
andbCom a b = trivial

-- Exercise 1 ------------------------------------------------------------------

{-@ reflect nandb @-}
nandb :: Bool -> Bool -> Bool
nandb a b = negb (andb a b)

{-@ testNand1 :: { nandb True True == False }  @-}
testNand1 = trivial

{-@ testNand2 :: { nandb True False == True }  @-}
testNand2 = trivial

{-@ testNand3 :: { nandb False True == True }  @-}
testNand3 = trivial

{-@ testNand4 :: { nandb False False == True } @-}
testNand4 = trivial

-- Exercise 2 ------------------------------------------------------------------

{-@ reflect andb3 @-}
andb3 :: Bool -> Bool -> Bool -> Bool
andb3 a b c = andb (andb a b) c

{-@ testAnd31 :: { andb3 True True True == True }  @-}
testAnd31 = trivial

{-@ testAnd32 :: { andb3 False True True == False }  @-}
testAnd32 = trivial

{-@ testAnd33 :: { andb3 True False True == False }  @-}
testAnd33 = trivial

{-@ testAnd34 :: { andb3 True True False == False }  @-}
testAnd34 = trivial

--------------------------------------------------------------------------------
-- | Peano ---------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect even @-}
even :: Peano -> Bool
even O         = True
even (S O)     = False
even (S (S n)) = even n

{-@ test_Even0 :: { even O == True } @-}
test_Even0 :: Proof
test_Even0 = trivial

-- LH ISSUE #995
{-@ test_Even4 :: { even (S (S (S (S O)))) == True } @-}
test_Even4 :: Proof
test_Even4 = trivial

  -- =   even (S (S (S (S O))))
  -- ==. even (S (S O))
  -- ==. even O
  -- ==. True
  -- *** QED

{-@ test_Even5 :: { even (S (S (S (S (S O))))) = False } @-}
test_Even5 :: Proof
test_Even5 = trivial

  -- =   even (S (S (S (S (S O)))))
  -- ==. even (((S (S (S O)))))
  -- ==. even (((((S O)))))
  -- ==. False
  -- *** QED

-- | Plus & Mult ---------------------------------------------------------------

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

{-@ reflect mult @-}
mult :: Peano -> Peano -> Peano
mult n m = case n of
  O    -> O
  S O  -> m
  S n' -> plus m (mult n' m)

{- TODO:trivial testPlus1 :: { plus (S (S O)) O == (S (S O)) } @-}
testPlus1 = trivial

{- TODO:trivial testMult1 :: { mult (S (S O)) (S (S O)) == (S (S (S (S O)))) } @-}
testMult1 = trivial

-- | Factorial -----------------------------------------------------------------

{-@ reflect factorial @-}
factorial :: Peano -> Peano
factorial O     = O
factorial (S O) = S O
factorial (S n) = mult (S n) (factorial n)

{- TODO:trivial testFactorial1 :: { factorial (S (S (S O)))  == S (S (S (S (S (S O))))) } @-}
testFactorial1 = trivial

-- | Peano Comparisons ---------------------------------------------------------

{-@ reflect beq @-}
beq :: Peano -> Peano -> Bool
beq O     O     = True
beq (S m) (S n) = beq m n
beq _     _     = False

{-@ reflect ble @-}
ble :: Peano -> Peano -> Bool
ble O     _     = True
ble (S m) O     = False
ble (S m) (S n) = ble m n

{-@ testBle1 :: { ble (S (S O)) (S (S O))  == True } @-} -- TODO:trivial
testBle1 = trivial

  -- =   ble (S (S O)) (S (S O))
  -- ==. ble ((S O)) ((S O))
  -- ==. ble O O
  -- *** QED

{-@ testBle2 :: { ble (S (S O)) (S (S (S O)))  == True } @-} -- TODO:trivial
testBle2 = trivial

  -- =   ble (S (S O)) (S (S (S O)))
  -- ==. ble (S O) (S (S O))
  -- ==. ble O (S O)
  -- *** QED

{-@ testBle3 :: { ble  (S (S (S O))) (S (S O)) == False } @-} -- TODO:trivial
testBle3 = trivial
  -- =   ble (S (S (S O))) (S (S O))
  -- ==. ble (S (S O)) (S O)
  -- ==. ble (S O) O
  -- *** QED

-- | Exercise blt --------------------------------------------------------------

{-@ reflect blt @-}
blt :: Peano -> Peano -> Bool
blt O     O     = False
blt O     (S n) = True
blt (S m) O     = False
blt (S m) (S n) = blt m n

{-@ testBlt1 :: { blt (S (S O)) (S (S O))  == False } @-} -- TODO:trivial
testBlt1 = trivial

  -- =   blt (S (S O)) (S (S O))
  -- ==. blt ((S O)) ((S O))
  -- ==. blt O O
  -- *** QED

{-@ testBlt2 :: { ble (S (S O)) (S (S (S O)))  == True } @-} -- TODO:trivial
testBlt2 = trivial

  -- =   ble (S (S O)) (S (S (S O)))
  -- ==. ble (S O) (S (S O))
  -- ==. ble O (S O)
  -- *** QED

{-@ testBlt3 :: { ble  (S (S (S O))) (S (S O)) == False } @-} -- TODO:trivial
testBlt3 = trivial

  -- =   ble (S (S (S O))) (S (S O))
  -- ==. ble (S (S O)) (S O)
  -- ==. ble (S O) O
  -- *** QED

-- | Proof by Simplification ---------------------------------------------------

{-@ thmPlus_O_l :: n:Peano -> { plus O n == n } @-}
thmPlus_O_l :: Peano -> Proof
thmPlus_O_l n = trivial

{-@ thmPlus_1_N :: n:Peano -> { plus (S O) n = S n } @-}
thmPlus_1_N :: Peano -> Proof
thmPlus_1_N n = trivial

{-@ thmMult_0_l :: n:Peano -> { mult O n = O } @-}
thmMult_0_l :: Peano -> Proof
thmMult_0_l n = trivial

-- | Proof by Simplification ---------------------------------------------------

{-@ thmPlusId :: a:Peano -> b:Peano -> { a = b => plus a a = plus b b } @-}
thmPlusId :: Peano -> Peano -> Proof
thmPlusId a b = trivial

{-@ thmPlusId' :: n:Peano -> m:Peano -> o:Peano -> { n = m => m = o => plus n m = plus m o } @-}
thmPlusId' :: Peano -> Peano -> Peano -> Proof
thmPlusId' n m o = trivial

{-@ thmMultOPlus :: n: Peano -> m: Peano -> { mult (plus O n) m = mult n m } @-}
thmMultOPlus :: Peano -> Peano -> Proof
thmMultOPlus n m = trivial

{-@ thmMultS1 :: m:Peano -> n:Peano -> { S n = m => mult m (S n) = mult m m } @-}
thmMultS1 :: Peano -> Peano -> Proof
thmMultS1 m n = trivial

-- | Proof by Case Analysis ----------------------------------------------------

{-@ thmPlus1Neq0 :: n:Peano -> { beq (plus n (S O)) O = False } @-}
thmPlus1Neq0 :: Peano -> Proof
thmPlus1Neq0 O     = trivial
thmPlus1Neq0 (S n) = trivial

{-@ thmNegbInvolutive :: b:Bool -> { negb (negb b) == b} @-}
thmNegbInvolutive :: Bool -> Proof
thmNegbInvolutive True  = trivial
thmNegbInvolutive False = trivial

{-@ thmAndbCom :: a:Bool -> b:Bool -> {andb a b == andb b a} @-}
thmAndbCom True  True  = trivial
thmAndbCom True  False = trivial
thmAndbCom False True  = trivial
thmAndbCom False False = trivial

{-@ thmAndbExch :: a:Bool -> b:Bool -> c:Bool
                -> { andb (andb a b) c == andb (andb a c) b }
  @-}
thmAndbExch :: Bool -> Bool -> Bool -> Proof
thmAndbExch True  True  True  = trivial
thmAndbExch True  True  False = trivial
thmAndbExch True  False True  = trivial
thmAndbExch True  False False = trivial
thmAndbExch False True  True  = trivial
thmAndbExch False True  False = trivial
thmAndbExch False False True  = trivial
thmAndbExch False False False = trivial

{-@ thmAndbTrueElim2 :: b:Bool -> c:Bool -> { andb b c = True => c = True } @-} -- TODO:trivial
thmAndbTrueElim2 :: Bool -> Bool -> Proof
thmAndbTrueElim2 False False = andb False False *** QED
thmAndbTrueElim2 False True  = andb False True  *** QED
thmAndbTrueElim2 True  False = andb True  False *** QED
thmAndbTrueElim2 True  True  = andb True  True  *** QED

{-@ thm0NeqPlus1 :: n:Peano -> { beq O (plus n (S O)) = False } @-}
thm0NeqPlus1 :: Peano -> Proof
thm0NeqPlus1 O     = trivial
thm0NeqPlus1 (S n) = trivial


{-@ thmIdTwice :: f:(x:Bool -> {v:Bool | v = x}) -> b:Bool -> { f (f b) = b } @-}
thmIdTwice :: (Bool -> Bool) -> Bool -> Proof
thmIdTwice f b
  =   f (f b)
  ==. b
  *** QED

{-@ thmNegTwice :: f:(x:Bool -> {v:Bool | v = negb x}) -> b:Bool -> { f (f b) = b } @-}
thmNegTwice :: (Bool -> Bool) -> Bool -> Proof
thmNegTwice f b
  =   f (f b)
  ==. b ? thmNegbInvolutive b
  *** QED

-- RJ: You can rewrite
--   (m : Peano) -> (n : Peano) -> (eqProof : m = n) -> (beq m n = True)

{-@ thmEqBeq :: m:Peano -> n:Peano -> { v : Proof |  m = n } -> { beq m n = True } @-}
thmEqBeq :: Peano -> Peano -> Proof -> Proof
thmEqBeq O O _         = trivial
thmEqBeq (S m) (S n) _ = thmEqBeq m n trivial
