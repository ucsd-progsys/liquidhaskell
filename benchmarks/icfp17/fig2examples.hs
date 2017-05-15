
module Blank where

import Fig2Lib (inc, dec, idd)

{-@ ex1 :: Nat -> Nat @-}
ex1 :: Int -> Int
ex1 x = let t = \z -> idd (dec x)
            y = t ()
        in inc y

{-@ ex2 :: Nat -> Nat @-} --ex2
ex2 :: Int -> Int
ex2 x = let ys _ = let n = dec x
                       p = inc x
                       xs = n : []
                   in p : xs
            y = head (ys ())
        in inc y

{-@ ex3 :: Nat -> Nat @-}
ex3 :: Int -> Int
ex3 = let fn = \a -> dec a
          fp = \b -> inc b
      in fp . fn

{-@ ex4 :: [Nat] -> [Nat] @-}
ex4 :: [Int] -> [Int]
ex4 = let fn = \a -> dec a
          fp = \b -> inc b
      in map fp . map fn
