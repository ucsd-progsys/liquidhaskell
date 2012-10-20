module spec GHC.Classes where

-- TODO: Drop prefix below


assume GHC.Classes.&&      :: x: Bool -> y: Bool    -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
assume GHC.Classes.==      :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume GHC.Classes./=      :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume GHC.Classes.>       :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume GHC.Classes.>=      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume GHC.Classes.<       :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume GHC.Classes.<=      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> x = y) && ((v = LT) <=> x < y) && ((v = GT) <=> x > y))}
assume max                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x > y) ? x : y) }
assume min                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x < y) ? x : y) }
