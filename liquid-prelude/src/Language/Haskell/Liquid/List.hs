{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Language.Haskell.Liquid.List (transpose) where

{-@ lazy transpose @-}
transpose                  :: Int -> [[a]] -> [[a]]
transpose _ []             = []
transpose n ([]   : xss)   = transpose n xss
transpose n ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n - 1) (xs : [ t | (_:t) <- xss])
