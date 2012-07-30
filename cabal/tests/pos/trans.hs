module Tx where

import Language.Haskell.Liquid.Prelude

{-@ include <trans.hs.hquals> @-}

{- assert getHeads   :: xs:[{v:[a]| len(v) > 0}] -> {v:[a] | len(v) = len(xs)} @-}
getHeads ((h:_): xss) = h : getHeads xss
getHeads ([]   : xss) = getHeads xss
getHeads []           = []
-- NEEDS TAGS: getHeads xss = [ h | (h:_) <- xss]

{- assert getTails   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
getTails :: Int -> [[a]] -> [[a]]
getTails n ((_:t): xss) = t : getTails n xss
getTails n ([]   : xss) = getTails n xss
getTails n []           = []
-- NEEDS TAGS: getTails n xss = liquidAssert (n > 0) [t | (_:t) <- xss]

{-@ assert transpose :: n:{v: Int | v >= 0} -> m:{v:Int|v >= 0} -> {v:[{v:[a] | len(v) = n}] | len(v) = m} -> {v:[{v:[a] | len(v) = m}] | len(v) = n} @-}
transpose :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : getHeads xss) : transpose (n - 1) m (xs : getTails n xss)

-- NEEDS TAGS: transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n-1) m (xs : [ t | (_:t) <- xss]) 
-- get this to work with:
-- map tail
-- map head
{- qualif .... -}

