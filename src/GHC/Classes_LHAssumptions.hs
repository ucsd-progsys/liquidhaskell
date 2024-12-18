{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Classes_LHAssumptions where

import GHC.Types_LHAssumptions()

{-@

assume not :: x:Bool -> {v:Bool | ((v) <=> ~(x))}
assume &&    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) && (y)))}
assume ||    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) || (y)))}
assume ==    :: (Eq  a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x = y)}
assume /=    :: (Eq  a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x != y)}
assume >     :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x > y)}
assume >=    :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x >= y)}
assume <     :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x < y)}
assume <=    :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x <= y)}

assume compare :: (Ord a) => x:a -> y:a
        -> {v:Ordering | (((v = EQ) <=> (x = y)) &&
                                    ((v = LT) <=> (x < y)) &&
                                    ((v = GT) <=> (x > y))) }

assume max :: (Ord a) => x:a -> y:a -> {v:a | v = (if x > y then x else y) }
assume min :: (Ord a) => x:a -> y:a -> {v:a | v = (if x < y then x else y) }

@-}
