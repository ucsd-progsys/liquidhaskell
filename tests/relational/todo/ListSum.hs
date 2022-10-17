{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Twice where
import           Prelude                 hiding ( sum
                                                , length
                                                )


thm :: [Int] -> [Int] -> ()
{-@ thm :: xs:[Int] -> ys:{[Int] | prop xs ys && length ys == length xs } -> {sum xs == 2 * sum ys } @-}
thm []       []       = ()
thm (x : xs) (y : ys) = thm xs ys

{-@ measure sum @-}
sum :: [Int] -> Int
sum []       = 0
sum (x : xs) = x + sum xs

{-@ measure length @-}
length :: [a] -> Int
length []       = 0
length (x : xs) = 1 + length xs

{-@ reflect prop @-}
prop :: [Int] -> [Int] -> Bool
prop []       []       = True
prop (x : xs) (y : ys) = x == 2 * y && prop xs ys
prop _        _        = False
