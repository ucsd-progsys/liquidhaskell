{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Classes_LHAssumptions where

import GHC.Classes
import GHC.Types_LHAssumptions()

{-@

assume GHC.Classes.not :: x:Bool -> {v:Bool | ((v) <=> ~(x))}
assume (GHC.Classes.&&)    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) && (y)))}
assume (GHC.Classes.||)    :: x:Bool -> y:Bool
        -> {v:Bool | ((v) <=> ((x) || (y)))}
assume (GHC.Classes.==)    :: (Eq  a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x = y)}
assume (GHC.Classes./=)    :: (Eq  a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x != y)}
assume (GHC.Classes.>)     :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x > y)}
assume (GHC.Classes.>=)    :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x >= y)}
assume (GHC.Classes.<)     :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x < y)}
assume (GHC.Classes.<=)    :: (Ord a) => x:a -> y:a
        -> {v:Bool | ((v) <=> x <= y)}

assume GHC.Classes.compare :: (Ord a) => x:a -> y:a
        -> {v:Ordering | (((v = EQ) <=> (x = y)) &&
                                    ((v = LT) <=> (x < y)) &&
                                    ((v = GT) <=> (x > y))) }

assume GHC.Classes.max :: (Ord a) => x:a -> y:a -> {v:a | v = (if x > y then x else y) }
assume GHC.Classes.min :: (Ord a) => x:a -> y:a -> {v:a | v = (if x < y then x else y) }

@-}
