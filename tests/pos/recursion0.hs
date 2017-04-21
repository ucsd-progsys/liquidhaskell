module Main where

main :: IO ()
main = return ()

{-@ total :: Nat -> Nat @-}
total :: Int -> Int 
total 0 = 0
total n = 1 + total (n-1)

