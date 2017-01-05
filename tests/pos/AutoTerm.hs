module Isort where

data SortedList a =
     Mt
   | Ln{h :: a, t :: SortedList a}

{-@ data SortedList [sortedlen] @-}


{-@ measure sortedlen @-}
{-@ sortedlen :: SortedList a -> {v:Int | v >= 0 } @-}
sortedlen :: SortedList a -> Int
sortedlen Mt = 0
sortedlen (Ln x xs) = 1 + sortedlen xs

{-@ insert :: (Ord a) => a -> lst:(SortedList a) -> {v: SortedList a | sortedlen v = sortedlen lst + 1} / [sortedlen lst]@-}
insert :: (Ord a) => a -> SortedList a -> SortedList a
insert x Mt = Ln x Mt
insert y (Ln x xs)
  | y < x     = Ln y (Ln x xs)
  | otherwise = Ln x (insert y xs)

{-@ isort :: (Ord a) => lst:[a] -> {v : SortedList a | sortedlen v = len lst} @-}
isort :: (Ord a) => [a] -> SortedList a
isort [] = Mt -- note can't use [] here
isort (x:xs) = insert x (isort xs)
