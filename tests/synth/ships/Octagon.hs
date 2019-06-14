{-# LANGUAGE RecordWildCards #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--typed-holes" @-}

module Octagon where

import Prelude hiding (abs)

{-@ type OctCoefficient = {v : Int | v == -1 || v == 1} @-}
type OctCoefficient = Int

data OctConstraint = OctConstraint {
      ocV1    :: OctCoefficient
    , ocV2    :: OctCoefficient
    , ocConst :: Int
    }

{-@ reflect constraintNN @-}
constraintNN :: OctConstraint -> Bool
constraintNN OctConstraint{..} = ocV1 == (-1) && ocV2 == (-1)

{-@ reflect constraintPP @-}
constraintPP :: OctConstraint -> Bool
constraintPP OctConstraint{..} = ocV1 == 1 && ocV2 == 1

{-@ reflect constraintNP @-}
constraintNP :: OctConstraint -> Bool
constraintNP OctConstraint{..} = ocV1 == (-1) && ocV2 == 1

{-@ reflect constraintPN @-}
constraintPN :: OctConstraint -> Bool
constraintPN OctConstraint{..} = ocV1 == 1 && ocV2 == (-1)

{-@ reflect checkOctConstraint @-}
checkOctConstraint :: Int -> Int -> OctConstraint -> Bool
checkOctConstraint x y OctConstraint{..} = ocV1 * x + ocV2 * y <= ocConst

{-@
data IntOct = IntOct {
      ioC1 :: {v : OctConstraint | constraintNN v}
    , ioC2 :: {v : OctConstraint | constraintPP v}
    }
@-}
data IntOct = IntOct {
      ioC1 :: OctConstraint -- Lower bound
    , ioC2 :: OctConstraint -- Upper bound
    }

{-@ reflect betweenInt @-}
betweenInt :: Int -> IntOct -> Bool
betweenInt x IntOct{..} = 
       checkOctConstraint x 0 ioC1 
    && checkOctConstraint x 0 ioC2
    
{-@reflect subsetInt @-}
subsetInt :: IntOct -> IntOct -> Bool
subsetInt (IntOct (OctConstraint (-1) (-1) l1) (OctConstraint 1 1 u1)) (IntOct (OctConstraint (-1) (-1) l2) (OctConstraint 1 1 u2)) = l1 <= l2 && u1 <= u2

{-@
data Loc = Loc {
      x :: Int
    , y :: Int
    }
@-}
data Loc = Loc {
      x :: Int
    , y :: Int
    }

{-@
data LocOct = LocOct {
      loC1 :: {v:OctConstraint | constraintNN v}
    , loC2 :: {v:OctConstraint | constraintNP v}
    , loC3 :: {v:OctConstraint | constraintPP v}
    , loC4 :: {v:OctConstraint | constraintPP v}
    , loC5 :: {v:OctConstraint | constraintPP v}
    , loC6 :: {v:OctConstraint | constraintPN v}
    , loC7 :: {v:OctConstraint | constraintNN v}
    , loC8 :: {v:OctConstraint | constraintNN v}
    }
@-}
data LocOct = LocOct {
      loC1 :: OctConstraint -- Left
    , loC2 :: OctConstraint -- Top left
    , loC3 :: OctConstraint -- Top
    , loC4 :: OctConstraint -- Top right
    , loC5 :: OctConstraint -- Right
    , loC6 :: OctConstraint -- Bottom right
    , loC7 :: OctConstraint -- Bottom
    , loC8 :: OctConstraint -- Bottom left
    }

{-@ reflect betweenLoc @-}
betweenLoc :: Loc -> LocOct -> Bool
betweenLoc Loc{..} LocOct{..} = 
       checkOctConstraint x 0 loC1
    && checkOctConstraint x y loC2
    && checkOctConstraint 0 y loC3
    && checkOctConstraint x y loC4
    && checkOctConstraint x 0 loC5
    && checkOctConstraint x y loC6
    && checkOctConstraint 0 y loC7
    && checkOctConstraint x y loC8

{-@ reflect subsetLoc @-}
subsetLoc :: LocOct -> LocOct -> Bool
subsetLoc (LocOct 
            (OctConstraint _ _ c1_1) 
            (OctConstraint _ _ c2_1)
            (OctConstraint _ _ c3_1)
            (OctConstraint _ _ c4_1)
            (OctConstraint _ _ c5_1)
            (OctConstraint _ _ c6_1)
            (OctConstraint _ _ c7_1)
            (OctConstraint _ _ c8_1))
          (LocOct
            (OctConstraint _ _ c1_2) 
            (OctConstraint _ _ c2_2)
            (OctConstraint _ _ c3_2)
            (OctConstraint _ _ c4_2)
            (OctConstraint _ _ c5_2)
            (OctConstraint _ _ c6_2)
            (OctConstraint _ _ c7_2)
            (OctConstraint _ _ c8_2)) = 
                 c1_1 <= c1_2
              && c2_1 <= c2_2
              && c3_1 <= c3_2
              && c4_1 <= c4_2
              && c5_1 <= c5_2
              && c6_1 <= c6_2
              && c7_1 <= c7_2
              && c8_1 <= c8_2



{-@
data Ship = Ship {
      shipCapacity :: Int
    , shipLoc :: Loc
    }
@-}
data Ship = Ship {
      shipCapacity :: Int
    , shipLoc :: Loc
    }

data ShipOct = ShipOct {
      shipCapacityD :: IntOct
    , shipLocD :: LocOct
    }

{-@ reflect betweenShip @-}
betweenShip :: Ship -> ShipOct -> Bool
betweenShip Ship{..} ShipOct{..} = betweenInt shipCapacity shipCapacityD && betweenLoc shipLoc shipLocD

{-@ reflect subsetShip @-}
subsetShip :: ShipOct -> ShipOct -> Bool
subsetShip (ShipOct c1 l1) (ShipOct c2 l2) = subsetInt c1 c2 && subsetLoc l1 l2



{-@ reflect atLeast @-}
atLeast :: Ship -> Bool
atLeast z = shipCapacity z > b
    where
        b = 50

{-@ reflect abs @-}
abs :: Int -> Int
abs i | i < 0 = -1 * i
abs i         = i

{-@ reflect nearby @-}
nearby :: Ship -> Bool
nearby (Ship _ z) = abs (x z - x l) + abs (y z - y l) <= d
    where
        l = Loc 200 200
        d = 100

{-@ reflect ok @-}
ok :: Ship -> Bool
ok z = atLeast z && nearby z




{-@ adversarySound1
 :: secret : Ship
 -> {prior : ShipOct | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipOct | betweenShip secret post => response == atLeast secret && subsetShip post prior}
@-}
adversarySound1 :: Ship -> ShipOct -> Bool -> ShipOct
adversarySound1 secret (ShipOct (IntOct (OctConstraint (-1) (-1) l) (OctConstraint 1 1 u)) loc) res = _adversarySound1
-- adversarySound1 secret (ShipOct (IntOct (OctConstraint (-1) (-1) l) u) loc) True = 
--     ShipOct (IntOct (OctConstraint (-1) (-1) (min l l')) u) loc
-- 
--     where
--         l' = (-51)
-- adversarySound1 secret (ShipOct (IntOct l (OctConstraint 1 1 u)) loc) False = 
--     ShipOct (IntOct l (OctConstraint 1 1 (min u u'))) loc
-- 
--     where
--         u' = 50


{-@ adversaryComplete1
 :: secret : Ship
 -> {prior : ShipOct | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipOct | response == atLeast secret => betweenShip secret post && subsetShip post prior}
@-}
adversaryComplete1 :: Ship -> ShipOct -> Bool -> ShipOct
adversaryComplete1 secret (ShipOct (IntOct (OctConstraint (-1) (-1) l) (OctConstraint 1 1 u)) loc) res = _adversaryComplete1
-- adversaryComplete1 secret (ShipOct (IntOct (OctConstraint (-1) (-1) l) u) loc) True = 
--     ShipOct (IntOct (OctConstraint (-1) (-1) (min l l')) u) loc
-- 
--     where
--         l' = (-51)
-- adversaryComplete1 secret (ShipOct (IntOct l (OctConstraint 1 1 u)) loc) False = 
--     ShipOct (IntOct l (OctConstraint 1 1 (min u u'))) loc
-- 
--     where
--         u' = 50

{-@ adversarySound2
 :: secret : Ship
 -> {prior : ShipOct | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipOct | betweenShip secret post => response == nearby secret && subsetShip post prior}
@-}
adversarySound2 :: Ship -> ShipOct -> Bool -> ShipOct
adversarySound2 secret (ShipOct cap (LocOct 
    c1 
    (OctConstraint (-1)    1 c2)
    c3
    (OctConstraint    1    1 c4)
    c5
    (OctConstraint    1 (-1) c6)
    c7
    (OctConstraint (-1) (-1) c8)
    )) res = _adversarySound2
-- adversarySound2 secret (ShipOct cap (LocOct 
--     c1 
--     (OctConstraint (-1)    1 c2)
--     c3
--     (OctConstraint    1    1 c4)
--     c5
--     (OctConstraint    1 (-1) c6)
--     c7
--     (OctConstraint (-1) (-1) c8)
--     )) True = 
--         let loc = LocOct
--                     c1
--                     (OctConstraint (-1)    1 (min 100 c2))
--                     c3
--                     (OctConstraint    1    1 (min 500 c4))
--                     c5
--                     (OctConstraint    1 (-1) (min 100 c6))
--                     c7
--                     (OctConstraint (-1) (-1) (min (-300) c8))
--         in
--         ShipOct cap loc
-- 
-- adversarySound2 secret (ShipOct cap (LocOct
--     c1 
--     c2
--     c3
--     c4
--     c5
--     c6
--     c7
--     (OctConstraint (-1) (-1) c8)
--     )) False = 
-- 
--         -- There are 4 options here.
--         -- Choosing the top-right arbitrarily. 
--         let loc = LocOct
--                     c1
--                     c2
--                     c3
--                     c4
--                     c5
--                     c6
--                     c7
--                     (OctConstraint (-1) (-1) (min (-501) c8))
--         in
--         ShipOct cap loc

{-@ adversaryComplete2
 :: secret : Ship
 -> {prior : ShipOct | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipOct | response == nearby secret => betweenShip secret post && subsetShip post prior}
@-}
adversaryComplete2 :: Ship -> ShipOct -> Bool -> ShipOct
adversaryComplete2 secret (ShipOct cap (LocOct 
    c1 
    (OctConstraint (-1)    1 c2)
    c3
    (OctConstraint    1    1 c4)
    c5
    (OctConstraint    1 (-1) c6)
    c7
    (OctConstraint (-1) (-1) c8)
    )) res = _adversaryComplete2
-- adversaryComplete2 secret (ShipOct cap (LocOct 
--     c1 
--     (OctConstraint (-1)    1 c2)
--     c3
--     (OctConstraint    1    1 c4)
--     c5
--     (OctConstraint    1 (-1) c6)
--     c7
--     (OctConstraint (-1) (-1) c8)
--     )) True = 
--         let loc = LocOct
--                     c1
--                     (OctConstraint (-1)    1 (min 100 c2))
--                     c3
--                     (OctConstraint    1    1 (min 500 c4))
--                     c5
--                     (OctConstraint    1 (-1) (min 100 c6))
--                     c7
--                     (OctConstraint (-1) (-1) (min (-300) c8))
--         in
--         ShipOct cap loc
-- 
-- adversaryComplete2 secret ship False =
-- 
--     -- Bad, but complete posterior.
--     ship


















assert :: Bool -> Proof
{-@ assert :: b:{Bool | b} -> {v:Proof | b} @-}
assert _ = ()


use :: a -> Proof
use _ = ()

{-@ impl :: x:Bool -> y:Bool -> {v:Bool | v <=> (x => y)} @-}
impl :: Bool -> Bool -> Bool
impl a b = if a then b else True

{-@ iff :: x:Bool -> y:Bool -> {v:Bool | v <=> (x <=> y)} @-}
iff :: Bool -> Bool -> Bool
iff a b = (if a then b else True) && if b then a else True


assume :: Bool -> Proof
{-@ assume assume :: b:Bool -> {v:Proof | b} @-}
assume _ = ()

type Proof = ()


-- | p *** QED casts p into a proof

data QED = QED

infixl 2 ***
x *** QED = ()


-------------------------------------------------------------------------------
-- | Equational Reasoning -----------------------------------------------------
-------------------------------------------------------------------------------

-- use (==.) not to check intermediate steps

infixl 3 ==.

(==.) :: a -> a -> a
_ ==. x = x
{-# INLINE (==.) #-}

infixl 2 =>.

(=>.) :: Bool -> Bool -> Bool
_ =>. x = x
{-# INLINE (=>.) #-}


infixl 2 <=.

(<=.) :: Bool -> Bool -> Bool
_ <=. x = x
{-# INLINE (<=.) #-}

-- Explanations: embed a proof into a term

infixl 3 ?
(?) :: a -> Proof -> a
x ? _ = x
{-# INLINE (?)   #-}

(&&&) :: Proof -> Proof -> Proof
x &&& _ = x


infixl 3 =/=
{-@ assume (=/=) :: x:a -> y:{a| x /= y } -> {v:a | v == x && v == y} @-}
(=/=) :: a -> a -> a
x =/= _  = x

infixl 3 ==?
{-@ assume (==?) :: x:a -> y:a -> {v:a | v == x && v == y} @-}
(==?) :: a -> a -> a
x ==? _  = x

infixl 3 ==!
{-@ (==!) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(==!) :: a -> a -> a
x ==! _  = x


infixl 4 ==:
{-@ (==:) :: x:a -> y:a -> {v:Proof | x == y} -> {v:a | v == x && v == y} @-}
(==:) :: a -> a -> Proof -> a
(==:) x _ _ = x

{-@ reflect cast @-}
{-@ cast :: b -> x:a -> {v:a | v == x } @-}
cast :: a -> b -> b
cast _ y = y

