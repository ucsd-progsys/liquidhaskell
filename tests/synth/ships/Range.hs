{-# LANGUAGE RecordWildCards #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--typed-holes" @-}

module Range where

import Prelude hiding (abs)

data IntRange = IntRange {
      lower :: Int
    , upper :: Int
    }

{-@ reflect betweenInt @-}
betweenInt :: Int -> IntRange -> Bool
betweenInt x IntRange{..} = lower < x && x < upper

{-@ reflect subsetInt @-}
subsetInt :: IntRange -> IntRange -> Bool
subsetInt (IntRange l1 u1) (IntRange l2 u2) = l1 >= l2 && u1 <= u2

{-@ subsetIntProof :: i : Int -> r1 : IntRange -> {r2 : IntRange | subsetInt r1 r2} -> {betweenInt i r1 => betweenInt i r2} @-}
subsetIntProof :: Int -> IntRange -> IntRange -> ()
subsetIntProof i r1 r2 = ()

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

data LocRange = LocRange {
      xD :: IntRange
    , yD :: IntRange
    }

{-@ reflect betweenLoc @-}
betweenLoc :: Loc -> LocRange -> Bool
betweenLoc Loc{..} LocRange{..} = betweenInt x xD && betweenInt y yD

{-@ reflect subsetLoc @-}
subsetLoc :: LocRange -> LocRange -> Bool
subsetLoc (LocRange x1 y1) (LocRange x2 y2) = subsetInt x1 x2 && subsetInt y1 y2

{-@ subsetLocProof :: l : Loc -> r1 : LocRange -> {r2 : LocRange | subsetLoc r1 r2} -> {betweenLoc l r1 => betweenLoc l r2} @-}
subsetLocProof :: Loc -> LocRange -> LocRange -> ()
subsetLocProof l r1 r2 = ()

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

{-@ reflect betweenShip @-}
betweenShip :: Ship -> ShipRange -> Bool
betweenShip Ship{..} ShipRange{..} = betweenInt shipCapacity shipCapacityD && betweenLoc shipLoc shipLocD

{-@ reflect subsetShip @-}
subsetShip :: ShipRange -> ShipRange -> Bool
subsetShip (ShipRange c1 l1) (ShipRange c2 l2) = subsetInt c1 c2 && subsetLoc l1 l2

{-@ subsetShipProof :: s : Ship -> r1 : ShipRange -> {r2 : ShipRange | subsetShip r1 r2} -> {betweenShip s r1 => betweenShip s r2} @-}
subsetShipProof :: Ship -> ShipRange -> ShipRange -> ()
subsetShipProof _ _ _ = ()

data ShipRange = ShipRange {
      shipCapacityD :: IntRange
    , shipLocD :: LocRange
    }

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
 -> {prior : ShipRange | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipRange | betweenShip secret post => response == atLeast secret && subsetShip post prior}
@-}
adversarySound1 :: Ship -> ShipRange -> Bool -> ShipRange
adversarySound1 secret (ShipRange (IntRange l u) loc) res  = _adversarySound1
-- adversarySound1 secret (ShipRange (IntRange l u) loc) True  = ShipRange (IntRange (max 50 l) u) loc
-- adversarySound1 secret (ShipRange (IntRange l u) loc) False = ShipRange (IntRange l (min 51 u)) loc

{-@ adversaryComplete1
 :: secret : Ship
 -> {prior : ShipRange | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipRange | response == atLeast secret => betweenShip secret post && subsetShip post prior}
@-}
adversaryComplete1 :: Ship -> ShipRange -> Bool -> ShipRange
adversaryComplete1 secret (ShipRange (IntRange l u) loc) res  = _adversaryComplete1
-- adversaryComplete1 secret (ShipRange (IntRange l u) loc) True  = ShipRange (IntRange (max 50 l) u) loc
-- adversaryComplete1 secret (ShipRange (IntRange l u) loc) False = ShipRange (IntRange l (min 51 u)) loc

    
{-@ adversarySound2
 :: secret : Ship
 -> {prior : ShipRange | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipRange | betweenShip secret post => response == nearby secret && subsetShip post prior}
@-}
adversarySound2 :: Ship -> ShipRange -> Bool -> ShipRange
adversarySound2 secret (ShipRange c (LocRange (IntRange xl xu) (IntRange yl yu))) res = _adversarySound2
-- adversarySound2 secret (ShipRange c (LocRange (IntRange xl xu) (IntRange yl yu))) True = ShipRange c (LocRange (IntRange (max 149 xl) (min 251 xu)) (IntRange (max 149 yl) (min 251 yu)))
-- adversarySound2 secret (ShipRange c (LocRange (IntRange xl xu) (IntRange yl yu))) False = ShipRange c (LocRange (IntRange xl (min xu 150)) (IntRange yl (min 150 yu))) -- There are many different sound ranges here.

{-@ adversaryComplete2
 :: secret : Ship
 -> {prior : ShipRange | betweenShip secret prior}
 -> response : Bool
 -> {post : ShipRange | response == nearby secret => betweenShip secret post && subsetShip post prior}
@-}
adversaryComplete2 :: Ship -> ShipRange -> Bool -> ShipRange
adversaryComplete2 secret (ShipRange c (LocRange (IntRange xl xu) (IntRange yl yu))) res = _adversaryComplete2
-- adversaryComplete2 secret (ShipRange c (LocRange (IntRange xl xu) (IntRange yl yu))) True = ShipRange c (LocRange (IntRange (max 99 xl) (min xu 301)) (IntRange (max 99 yl) (min 301 yu)))
-- adversaryComplete2 secret (ShipRange c loc) False = ShipRange c loc



