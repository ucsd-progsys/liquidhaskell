{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}
module T1659 where

{-@
data LWW  = LWW {
    lwwTime  :: Int
  }
@-}
data LWW  = LWW  {lwwTime :: Int}


type family Operation t = op
type instance Operation LWW = LWW


-- crash: SMTLIB2 respSat = Error "line 296 column 77: Sorts Main.LWW and Int are incompatible"
{-@ claw :: x : Operation LWW -> { x /= x} @-}
claw :: Operation LWW -> ()
claw (LWW t0) = ()

-- ok. unsafe. `Operation LWW` changed to `LWW`
{-@ claw2 :: x : LWW -> { x /= x} @-}
claw2 :: LWW -> ()
claw2 x@(LWW t0) = ()

-- ok. unsafe. No pattern matching
{-@ claw3 :: x : Operation LWW -> { x /= x} @-}
claw3 :: Operation LWW -> ()
claw3 x = ()
