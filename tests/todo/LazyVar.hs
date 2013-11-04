module LazyVar where

{-@ foo :: a -> Bool @-}
foo :: a -> Bool
foo = undefined

{-@ bar :: [a] -> Nat -> a @-}
bar :: [a] -> Int -> a
bar xs i
  | i < l && foo x = x
  | otherwise      = undefined
  where
    l = length xs
    {-@ LAZYVAR x @-}
    x = xs !! i
