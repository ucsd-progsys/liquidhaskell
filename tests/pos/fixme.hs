{-@ LIQUID "--higherorder"     @-}

module Nat where

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect fib @-}
fib :: Int -> Int
fib n = n

{-@ poof :: n:Int -> {n == fib n } @-}
poof n = n ==. fib n  ? poof n
        *** QED
