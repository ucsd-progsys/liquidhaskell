
module Blank where

{-@ inc :: x:Int -> {v:Int | v = x+1} @-}
inc :: Int -> Int
inc x = x + 1

{-@ dec :: x:Int -> {v:Int | v = x-1} @-}
dec :: Int -> Int
dec x = x - 1

{-@ ex1 :: Nat -> Nat @-}
ex1 :: Int -> Int
ex1 x = let y = let t = x
                in dec t
        in inc y

{-@ ex2 :: Nat -> Nat @-}
ex2 :: Int -> Int
ex2 x = let ys = let n  = dec x
                     p  = inc x
                     xs = n : []
                 in p : xs
            y = head ys
        in inc y

{-@ ex3 :: Nat -> Nat @-}
ex3 :: Int -> Int
ex3 = let fn = \a -> dec a
          fp = \b -> inc b
      in fp . fn

{-@ ex4 :: [Nat] -> [Nat] @-}
ex4 :: [Int] -> [Int]
ex4 = let fn = \a -> dec a
          fp = \b -> dec b
      in map fp . map fn
