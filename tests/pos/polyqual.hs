module Poo (nearestCenter) where

import Data.List (minimumBy)

data WrapType b a = WrapType {getVect :: b, getVal :: a}

{-@ type List a N     = {v : [a] | (len v) = N} @-}
{-@ type Point N      = List Double N           @-}
{-@ type GenPoint a N = WrapType (Point N) a    @-}


{-@ nearestCenter :: n:Int -> (GenPoint a n) -> [(Point n)] -> (Point n) @-} 
nearestCenter     :: Int -> WrapType [Double] a -> [[Double]] -> [Double] 
nearestCenter n x = minKey . map (\c -> (c, distance c (getVect x)))

minKey  :: (Ord v) => [(k, v)] -> k
minKey  = fst . minimumBy (\x y -> compare (snd x) (snd y)) 

{- distance :: a:[Double] -> {v:[Double] | (len v) = (len a)} -> Double -}
distance     :: [Double] -> [Double] -> Double 
distance a b = sqrt . sum $ safeZipWith (\v1 v2 -> (v1 - v2) ^ 2) a b

{-@ safeZipWith :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs)) @-}
safeZipWith f (a:as) (b:bs) = f a b : safeZipWith f as bs
safeZipWith _ [] []         = []


