module Blank where

{-@ type BNat X = {v:Nat | v < X} @-}

{-@ find :: (Eq a) => a -> xs:[a] -> Maybe (BNat {len xs}) @-}
find :: (Eq a) => a -> [a] -> Maybe Int
find x []     = Nothing 
find x (y:ys) 
  | x == y    = Just 0 
  | otherwise = (1 +) <$> find x ys
