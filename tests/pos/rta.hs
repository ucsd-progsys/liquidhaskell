module RTA where

{-@ predicate Goober X Y = X > Y @-}

{-@ inline goober @-}
goober :: (Ord a) => a -> a -> Bool
goober x y = x > y

{-@ type PosInline    a N = {v:a | goober v N} @-}

{-@ type PosPredicate a N = {v:a | Goober v N} @-}

{-@ incrI :: PosInline Int 0 -> PosInline Int 0 @-}
incrI :: Int -> Int
incrI x = x + 1

{-@ incrP :: PosPredicate Int 0 -> PosPredicate Int 0 @-}
incrP :: Int -> Int
incrP x = x + 1
