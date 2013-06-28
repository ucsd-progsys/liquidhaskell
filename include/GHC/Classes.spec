module spec GHC.Classes where

-- TODO: Drop prefix below
assume GHC.Types.EQ :: {v: GHC.Types.Ordering | v = (cmp v) }
assume GHC.Types.LT :: {v: GHC.Types.Ordering | v = (cmp v) }
assume GHC.Types.GT :: {v: GHC.Types.Ordering | v = (cmp v) }

measure cmp :: GHC.Types.Ordering -> GHC.Types.Ordering
cmp (GHC.Types.EQ) = { v | v = GHC.Types.EQ }
cmp (GHC.Types.LT) = { v | v = GHC.Types.LT }
cmp (GHC.Types.GT) = { v | v = GHC.Types.GT }


assume GHC.Classes.not     :: x: Bool -> {v: Bool | (Prop(v) <=> ~Prop(x))}
assume GHC.Classes.&&      :: x: Bool -> y: Bool    -> {v: Bool | (Prop(v) <=> (Prop(x) && Prop(y)))}
assume GHC.Classes.||      :: x: Bool -> y: Bool    -> {v: Bool | (Prop(v) <=> (Prop(x) || Prop(y)))}
assume GHC.Classes.==      :: (Eq  a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x = y)}
assume GHC.Classes./=      :: (Eq  a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x != y)}
assume GHC.Classes.>       :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x > y)}
assume GHC.Classes.>=      :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x >= y)}
assume GHC.Classes.<       :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x < y)}
assume GHC.Classes.<=      :: (Ord a) => x:a -> y:a -> {v:Bool | (Prop(v) <=> x <= y)}

assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = GHC.Types.EQ) <=> (x = y)) && 
                                                                      ((v = GHC.Types.LT) <=> (x < y)) &&
                                                                      ((v = GHC.Types.GT) <=> (x > y))) }
 
-- assume GHC.Classes.compare :: (Ord a) => x:a -> y:a -> {v:Ordering | (((v = GHC.Types.EQ) && ((cmp v) = GHC.Types.EQ) && (x = y)) || 
--                                                                       ((v = GHC.Types.LT) && ((cmp v) = GHC.Types.LT) && (x < y)) || 
--                                                                       ((v = GHC.Types.GT) && ((cmp v) = GHC.Types.GT) && (x > y))) }
 
assume max                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x > y) ? x : y) }
assume min                 :: (Ord a) => x:a -> y:a -> {v:a | v = ((x < y) ? x : y) }
