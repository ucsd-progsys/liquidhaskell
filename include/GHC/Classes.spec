module spec GHC.Classes where

-- TODO: Drop prefix below

measure EQ :: Ordering
measure LT :: Ordering
measure GT :: Ordering


measure cmp :: Ordering -> Ordering
cmp (EQ) = { v | v = EQ }
cmp (LT) = { v | v = LT }
cmp (GT) = { v | v = GT }


assume GHC.Classes.&&      :: x: Bool -> y: Bool    -> {v: Bool | ((? v) <=> ((? x) && (? y)))}
assume GHC.Classes.==      :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x = y)}
assume GHC.Classes./=      :: (Eq  a) => x:a -> y:a -> {v:Bool | ((? v) <=> x != y)}
assume GHC.Classes.>       :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x > y)}
assume GHC.Classes.>=      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x >= y)}
assume GHC.Classes.<       :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x < y)}
assume GHC.Classes.<=      :: (Ord a) => x:a -> y:a -> {v:Bool | ((? v) <=> x <= y)}
assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | ((((cmp v) = EQ) <=> x = y) && 
                                                                      (((cmp v) = LT) <=> x < y) && 
                                                                      (((cmp v) = GT) <=> x > y))}

assume max                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x > y) ? x : y) }
assume min                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x < y) ? x : y) }
