module Tx where

import Language.Haskell.Liquid.Prelude

{- include <len.hquals> -}

--{-@ assert compre :: xs:[a] -> {v:[(a,a)] | len(v) = len(xs) } @-}
--compre xs = [(x,x) | x <- xs]

--{-@ assert tx1      :: n:Int -> [{v:[a] | len(v) = n}] -> {v:[[a]] | len(v) = n} @-}
--tx1                 :: Int -> [[a]] -> [[a]]
--tx1 0 _              = []
--tx1 n ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : tx1 (n-1) (xs : [ t | (_:t) <- xss]) 

--{-@ assert tx2       :: m:Int -> {v:[[a]] | len(v) = m} -> [{v:[a] | len(v) = m}] @-}
--tx2                  :: Int -> [[a]] -> [[a]]
--tx2 m []             = []
--tx2 m ([]:_)         = []
--tx2 m ((x:xs) : xss) = (x : getHeads xss) : tx2 m (xs : getTails xss) 
-- tx2 m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : tx2 m (xs : [ t | (_:t) <- xss]) 
--tx2 m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : tx2 m (xs : [ t | (_:t) <- xss]) 

{-@ assert getHeads   :: xs:[{v:[a]| len(v) > 0}] -> {v:[a] | len(v) = len(xs)} @-}
getHeads xss = [ h | (h:_) <- xss]
--getHeads ((h:_): xss) = h : getHeads xss
--getHeads ([]   : xss) = getHeads xss
--getHeads []           = []

{-@ assert getTails   :: n:{v:Int | v > 0} -> xs:[{v:[a]| len(v) = n}] -> {v:[{v:[a] | len(v)=(n-1)}] | len(v) = len(xs)} @-}
getTails :: Int -> [[a]] -> [[a]]
getTails n xss = liquidAssert (n > 0) [t | (_:t) <- xss]

--getTails n ((_:t): xss) = t : getTails n xss
--getTails n ([]   : xss) = getTails n xss
--getTails n []           = []

{-@ assert tx3 :: n:{v: Int | v >= 0} -> m:{v:Int|v >= 0} -> {v:[{v:[a] | len(v) = n}] | len(v) = m} -> {v:[{v:[a] | len(v) = m}] | len(v) = n} @-}
tx3 :: Int -> Int -> [[a]] -> [[a]]
tx3 0 _ _              = []
tx3 n m ((x:xs) : xss) = liquidAssert (n > 0) 
                       $ liquidAssert (m > 0)
                         (x : getHeads xss) : tx3 (n - 1) m (xs : getTails n xss)

-- tx3 n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : tx3 (n-1) m (xs : [ t | (_:t) <- xss]) 

