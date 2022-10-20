module TyAbsMax where

import           Prelude                 hiding ( max )

{-@ max :: (Ord a, Eq a) => a -> a -> a @-}
max :: Ord a => a -> a -> a
max a b = if a < b then b else a

{-@ relational max ~ max :: x1:a -> y1:a -> a ~ x2:a -> y2:a -> a
                         | true => x1 = x2 => y1 = y2 => r1 x1 y1 = r2 x2 y2 @-}

{-@ relational max ~ max :: Ord a => x1:a -> y1:a -> a ~ Ord a => x2:a -> y2:a -> a
                         | true => x1 <= x2 => y1 <= y2 => r1 x1 y1 <= r2 x2 y2 @-}

{-@ relational max ~ max :: Ord a => x1:a -> y1:a -> a ~ Ord b => x2:b -> y2:b -> b
                         | true => true => x1 <= y1 && x2 <= y2 => r1 x1 y1 = y1 && r2 x2 y2 = y2 @-}