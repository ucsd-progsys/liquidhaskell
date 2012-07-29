module Tx where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ assert getHeads   :: xs:[{v:[a]| len(v) > 0}] -> {v:[a] | len(v) = len(xs)} @-}
getHeads xss = [ h | (h:_) <- xss]

{-@ assert getHeads'   :: xs:[{v:[a]| len(v) > 0}] -> {v:[a] | len(v) = len(xs)} @-}
getHeads' ((h:_): xss) = h : getHeads' xss
getHeads' ([]   : xss) = getHeads' xss
getHeads' []           = []

--{-@ assert getTails   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
--getTails :: Int -> [[a]] -> [[a]]
--getTails n ((_:t): xss) = t : getTails n xss
--getTails n ([]   : xss) = getTails n xss
--getTails n []           = []
--
--{-@ assert getTails'   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
--getTails' :: Int -> [[a]] -> [[a]]
--getTails' n xss = liquidAssert (n > 0) [t | (_:t) <- xss]
--
--{-@ assert getTails''   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
--getTails'' :: Int -> [[a]] -> [[a]]
--getTails'' n xss = [t | (_:t) <- xss]

