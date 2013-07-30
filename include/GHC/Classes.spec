module spec GHC.Classes where

import GHC.Types

assume GHC.Classes.not     :: x: Bool -> {v: Bool | (Prop(v) <=> ~Prop(x))}
assume GHC.Classes.&&      :: x: Bool -> y: Bool    -> {v:Bool | (Prop(v) <=> (Prop(x) && Prop(y)))}
assume GHC.Classes.||      :: x: Bool -> y: Bool    -> {v:Bool | (Prop(v) <=> (Prop(x) || Prop(y)))}
assume GHC.Classes.==      :: (Eq  a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x = y)}
assume GHC.Classes./=      :: (Eq  a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x != y)}
assume GHC.Classes.>       :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x > y)}
assume GHC.Classes.>=      :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x >= y)}
assume GHC.Classes.<       :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x < y)}
assume GHC.Classes.<=      :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x <= y)}

assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = EQ) <=> (x = y)) &&
                                                                      ((v = LT) <=> (x < y)) &&
                                                                      ((v = GT) <=> (x > y))) }

-- assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = GHC.Types.EQ) && ((cmp v) = GHC.Types.EQ) && (x = y)) ||
--                                                                       ((v = GHC.Types.LT) && ((cmp v) = GHC.Types.LT) && (x < y)) || 
--                                                                       ((v = GHC.Types.GT) && ((cmp v) = GHC.Types.GT) && (x > y))) }
 
assume max                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x > y) ? x : y) }
assume min                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x < y) ? x : y) }
