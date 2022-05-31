{-@ LIQUID "--expect-any-error" @-}

{-# LANGUAGE QuasiQuotes #-}

module Elim_ex_let (prop) where

import LiquidHaskell

[lq| type Nat = {v:Int | 0 <= v} |]

[lq| prop :: a -> Nat |]
prop _ = let x _ = let y = 0 
                   in
                     y - 3
         in 
           x () + 2
