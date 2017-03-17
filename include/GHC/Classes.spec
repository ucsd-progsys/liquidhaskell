module spec GHC.Classes where

import GHC.Types

not     :: x:GHC.Types.Bool -> {v:GHC.Types.Bool | ((v) <=> ~(x))}
(&&)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) && (y)))}
(||)    :: x:GHC.Types.Bool -> y:GHC.Types.Bool
        -> {v:GHC.Types.Bool | ((v) <=> ((x) || (y)))}
(==)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x = y)}
(/=)    :: (GHC.Classes.Eq  a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x != y)}
(>)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x > y)}
(>=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x >= y)}
(<)     :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x < y)}
(<=)    :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Bool | ((v) <=> x <= y)}

compare :: (GHC.Classes.Ord a) => x:a -> y:a
        -> {v:GHC.Types.Ordering | (((v = GHC.Types.EQ) <=> (x = y)) &&
                                    ((v = GHC.Types.LT) <=> (x < y)) &&
                                    ((v = GHC.Types.GT) <=> (x > y))) }

max :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x > y then x else y) }
min :: (GHC.Classes.Ord a) => x:a -> y:a -> {v:a | v = (if x < y then x else y) }
