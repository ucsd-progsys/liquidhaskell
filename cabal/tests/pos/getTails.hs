module Tx where

import Control.Exception (assert)

{-@ assert getTails   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
getTails :: Int -> [[a]] -> [[a]]
getTails n ((_:t): xss) = t : getTails n xss
getTails n ([]   : xss) = getTails n xss
getTails n []           = []

{-@ assert getTails'   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
getTails' :: Int -> [[a]] -> [[a]]
getTails' n xss = assert (n > 0) [t | (_:t) <- xss]

{-@ assert getTails''   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
getTails'' :: Int -> [[a]] -> [[a]]
getTails'' n xss = [t | (_:t) <- xss]

