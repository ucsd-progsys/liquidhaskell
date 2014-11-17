module Language.Haskell.Liquid.List (transpose) where

import Data.List hiding (transpose)

transpose                  :: Int -> [[a]] -> [[a]]
transpose n []             = []
transpose n ([]   : xss)   = transpose n xss
transpose n ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n - 1) (xs : [ t | (_:t) <- xss])


