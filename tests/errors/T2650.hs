{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection" @-}

-- | Tests that error messages show predicates that mix user-defined functions
-- with internal data constructor tests (is$) from inlined definitions.
-- See https://github.com/ucsd-progsys/liquidhaskell/issues/2650
--
-- Before the fix, the error would show just:
--   VV : T2650.State
-- (dropping the predicate entirely because it contained is$T2650.Empty).
--
-- After the fix, the required type shows the full predicate:
--   VV : {... | (if is$T2650.Empty VV then true else false) <=> T2650.isGood VV}

{-@ LIQUID "--expect-error-containing=T2650.isGood" @-}

module T2650 where

import Prelude

data State = Empty | NonEmpty

{-@ inline isEmpty @-}
isEmpty :: State -> Bool
isEmpty = \case
  Empty    -> True
  NonEmpty -> False

{-@ reflect isGood @-}
isGood :: State -> Bool
isGood Empty    = True
isGood NonEmpty = False

{-@
test ::
  s0 : State ->
  { s1 : State | isEmpty s1 <=> isGood s1 }
@-}
test :: State -> State
test x = x
