module RTA where

{-@ predicate Mouse X Y = X > Y @-}

{-@ inline mickey @-}
mickey :: (Ord a) => a -> a -> Bool
mickey x y = x > y

{-@ type PosInline    a N = {v:a | mickey v N} @-}

{-@ type PosPredicate a N = {v:a | Mouse v N} @-}

{-@ incrI :: PosInline Int 0 -> PosInline Int 0 @-}
incrI :: Int -> Int
incrI x = x + 1

{-@ incrP :: PosPredicate Int 0 -> PosPredicate Int 0 @-}
incrP :: Int -> Int
incrP x = x + 1
