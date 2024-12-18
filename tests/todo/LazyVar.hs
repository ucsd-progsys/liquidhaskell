module LazyVar where

{-@ foo :: a -> Bool @-}
foo :: a -> Bool
foo = undefined

{-@ bar :: [a] -> Nat -> a @-}
bar :: [a] -> Int -> a
bar xs i
  | i < l = x
  | otherwise      = undefined
  where
    l = length xs
    {-@ lazyvar x @-}
    x = xs !! i
