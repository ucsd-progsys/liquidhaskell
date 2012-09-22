module Language.Haskell.Liquid.List (transpose) where

import Data.List hiding (transpose)

{-# ANN transpose "forall a. n:Int -> xs:[{v:[a]|len(v) = n}] -> {v:[[a]] | len(v) = n}" #-}
transpose                  :: Int -> [[a]] -> [[a]]
transpose n []             = []
transpose n ([]   : xss)   = transpose n xss
transpose n ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n - 1) (xs : [ t | (_:t) <- xss])


