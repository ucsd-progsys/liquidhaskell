module Goo where
{-@ LIQUID "--short-names" @-}

{- amap :: forall <p :: Int -> Prop>.
              (Int -> Int<p>) -> [Int] -> [Int<p>] -}
amap          :: (Int -> b) -> [Int] -> [b]
amap f []     = []
amap f (x:xs) = f x : amap f xs

{-@ bob :: Int -> Nat @-}
bob :: Int -> Int
bob = undefined

{-@ foo :: [Int] -> [Nat] @-}
foo = amap bob
