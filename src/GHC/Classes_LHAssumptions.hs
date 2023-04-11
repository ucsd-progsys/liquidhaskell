module GHC.Classes_LHAssumptions where

import GHC.Classes()
import GHC.Types_LHAssumptions()

{-@

GHC.Classes.not :: x:GHC.Types.Bool -> {v:GHC.Types.Bool | ((v) <=> ~(x))}
(GHC.Classes.&&)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) && (y)))}
(GHC.Classes.||)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) || (y)))}
(GHC.Classes.==)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x = y)}
(GHC.Classes./=)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x != y)}
(GHC.Classes.>)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x > y)}
(GHC.Classes.>=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x >= y)}
(GHC.Classes.<)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x < y)}
(GHC.Classes.<=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x <= y)}

GHC.Classes.compare :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Ordering | (((v = GHC.Types.EQ) <=> (x = y)) &&
                                    ((v = GHC.Types.LT) <=> (x < y)) &&
                                    ((v = GHC.Types.GT) <=> (x > y))) }

GHC.Classes.max :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x > y then x else y) }
GHC.Classes.min :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x < y then x else y) }

@-}
