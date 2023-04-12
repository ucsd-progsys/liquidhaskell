module GHC.Classes_LHAssumptions where

import GHC.Classes()
import GHC.Types_LHAssumptions()

{-@

assume GHC.Classes.not :: x:GHC.Types.Bool -> {v:GHC.Types.Bool | ((v) <=> ~(x))}
assume (GHC.Classes.&&)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) && (y)))}
assume (GHC.Classes.||)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) || (y)))}
assume (GHC.Classes.==)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x = y)}
assume (GHC.Classes./=)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x != y)}
assume (GHC.Classes.>)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x > y)}
assume (GHC.Classes.>=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x >= y)}
assume (GHC.Classes.<)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x < y)}
assume (GHC.Classes.<=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x <= y)}

assume GHC.Classes.compare :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Ordering | (((v = GHC.Types.EQ) <=> (x = y)) &&
                                    ((v = GHC.Types.LT) <=> (x < y)) &&
                                    ((v = GHC.Types.GT) <=> (x > y))) }

assume GHC.Classes.max :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x > y then x else y) }
assume GHC.Classes.min :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x < y then x else y) }

@-}
