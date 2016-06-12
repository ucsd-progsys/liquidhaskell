
{-# LANGUAGE QuasiQuotes #-}

module ElimExLet (prop) where

import LiquidHaskell

[lq| type Nat = {v:Int | 0 <= v} |]

[lq| prop :: a -> Nat |]
prop _ = let x _ = let y = 0 
                   in
                     y - 1
         in 
           x () + 2
