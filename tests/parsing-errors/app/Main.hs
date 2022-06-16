-- This is here so parsing fails on Main.hs too!
{-@ id :: Foo:Int -> Int @-}

module Main where

main :: IO ()
main = putStrLn "Hello, Haskell!"
