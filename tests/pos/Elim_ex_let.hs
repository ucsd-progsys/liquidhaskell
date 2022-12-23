
{-# LANGUAGE QuasiQuotes #-}

module Elim_ex_let (prop) where

import LiquidHaskell

[lq| type MyNat = {v:Int | 0 <= v} |]

[lq| prop :: a -> MyNat |]
prop _ = let x _ = let y = 0 
                   in
                     y - 1
         in 
           x () + 2
