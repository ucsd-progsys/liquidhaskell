---
layout: post
title: "KMeans Clustering N-Dimensional Points"
date: 2013-02-14 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic measures 
demo: kmeans.hs
---

[Last time][safeList] we introduced a new specification called a *measure*
and demonstrated how to use it to encode the *length* of a list, and
thereby verify that functions like `head` and `tail` were only called with
non-empty lists (whose length was *strictly* greater than `0`.) As several
folks pointed out, once LiquidHaskell can reason about lengths, it can do a
lot more than just analyze non-emptiness. 

Indeed! 

So today, let me show you how one might implement a k-means algorithm that
clusters `n`-dimensional points into at most k groups, and how
LiquidHaskell can help us write and enforce these size requirements. 

<!-- For example, XXX pointed out that we can use the type
system to give an *upper* bound on the size of a list, e.g. 
using lists upper bounded by a gigantic `MAX_INT` value as
a proxy for finite lists.
-->

<!-- more -->

Rather than reinvent the wheel, lets start with an existing implementation
of K-Means, available [on hackage](hackage-kmeans). This may not be the most 
efficient implementation, but its a nice introduction to the algorithm, and we 
speculate that the general invariants will hold for more sophisticated
implementations.


\begin{code}

nearest centers x   = minimumKey distances
  where distances   = M.map (distance x) centers

minimumKey   :: (Ord v) => M.Map k v -> k
minimumKey   = fst . minimumBy (\x y -> compare (snd x) (snd y)) . M.toList 

distance     :: [Double] -> [Double] -> [Double]
distance a b = sqrt . sum $ zipWith (\x y -> (x - y) ^ 2) a b

normalize (n :: Int) = M.map (\(c, s) -> map (`safeDiv` s) c) 

initialCenters :: [a] -> M.HashMap Int [a] -> 

{-@ NNList a      = {v: [a] | ((len v) > 0) }           @-}
{-@ BoundInt  K   = {v: Int | (0 <= v) && (v < K) }     @-}
{-@ Point a   N   = {v: [a] | (len v) = N }             @-}
{-@ Points a  N   = NNList (Point a n)                  @-}
{-@ Cluster a K N = M.HashMap (BoundInt K) (Point a N)  @-}

{-@ initialCenters  :: k:{k:Int | k > 0} -> [a] -> M.HashMap (BoundInt k) (NNList a) @-}
initialCenters      :: Int -> [a] -> M.HashMap Int [a]  
initialCenters k xs = M.fromList $ zip indices partitions 
  where 
    clusterSize     = max 1 ((length points + k - 1) `div` k)
    parts           = partition clusterSize points
    nParts          = length parts
    indices         = liquidAssume (nParts <= k) [1..nParts]

{-@ partition        :: {v:Int | v > 0} -> [a] -> [(NNList a)] @-}
partition n []       = []
partition n ys@(_:_) = zs : part n zs' 
  where 
    zs               = take n ys
    zs'              = drop n ys

kmeansStep :: n:Int -> [Point Double n] -> M.Map k (Point Double n) -> M.Map k (Point Double n) 
kmeansStep (n :: Int) centers = M.fromList . mapReduce newCenter mergeCluster
  where
    recenter x              = [(nearest centers x, (x, 1))]
    merge (c1, s1) (c2, s2) = (zipWith (+) c1 c2, s1 + s2)

           
kmeans n k xs  = initialCenters k xs

-- kgroupBy :: k:Int -> (a -> BoundInt k) -> [a] -> {v: [(NNList a)] | (len v) <= k }
\end{code}



-- let rec ffor i j f = 
--   if i < j then (
--     f i; 
--     ffor (i+1) j f
--   )
-- 
-- let min_index a =
--   let min = ref 0 in
--   ffor 0 (Array.length a) (fun i ->
--     if a.(i) < a.(!min) then            (* ARRAY BOUNDS *)
--       min := i
--   );
--   !min
-- 
-- let nearest dist ctra x  =
--   let da = Array.map (dist x) ctra in
--   (min_index da, (x, 1))
-- 
-- let centroid plus p1 p2 = 
--   let (x1, size1) = p1 in
--   let (x2, size2) = p2 in 
--   (plus x1 x2, size1 + size2)
-- 
-- let update_centers div a ixs =
--   List.iter (fun (i, (x, size)) -> a.(i) <- div x size) ixs
--             (* ARRAY BOUNDS, DIV BY ZERO *)
-- 
-- let kmeans n dist plus div (points : 'a list) (centera : 'a array) =
--   assert (Array.length centera > 0); 
--   ffor 0 n begin fun _ ->
--     let point_centers   = map      (nearest dist centera) points      in
--     let center_clusters = group    point_centers                      in 
--     let new_centers     = reduce   (centroid plus) center_clusters    in
--     update_centers div centera new_centers
--   end  


\begin{code}

{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module Data.KMeans (kmeans, kmeansGen) where

import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)

{-@ groupBy :: (a -> a -> Bool) 
            -> [a] 
            -> [{v:[a] | len(v) > 0}] 
  @-}

groupBy           :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []     =  []
groupBy eq (x:xs) =  (x:ys) : groupBy eq zs
                     where (ys,zs) = span (eq x) xs

{-@ type Vec a N      = { v : [a] | (len v) = N } @-}

{-@ type Matrix a N M = Vec (Vec a N) M           @-}

{-@ type PosInt       = {v:Int | v > 0}           @-}


{-@ transpose :: n:Int -> m:PosInt -> Matrix a n m -> Matrix a m n @-}
transpose     :: Int -> Int -> [[a]] -> [[a]]

transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
-- transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"


data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect

-- dist ::  [Double] -> [Double] -> Double 
dist a b = sqrt . sum $ zipWith (\x y -> (x - y) ^ 2) a b      -- zipWith dimensions

safeDiv     :: (Fractional a) => a -> Int -> a
safeDiv n 0 = liquidError "divide by zero"
safeDiv n d = n / (fromIntegral d)


centroid n points = map ((`safeDiv` m) . sum) points'              -- divide By Zero
  where 
    m             = length points 
    points'       = transpose n m (map getVect points)


recluster n clusters = recluster' n centroids points 
  where 
    points         = concat clusters 
    centroids      = indexList $ map (centroid n) clusters
    centeredPoints = [(closest n centroids (getVect p), p) | p <- points]
    clusters'      = map (map snd)


recluster' n centroids points = map (map snd) $ groupBy ((==) `on` fst) reclustered
    where reclustered = sort [(closest n centroids (getVect p), p) | p <- points]


closest :: Int -> [(Int, [Double])] -> [Double] -> Int
closest (n :: Int) centroids point = minimumKey distances 
  where 
    distances = [(i, dist point ci) | (i, ci) <- icentroids ]

minimumKey :: (Ord v) => [(k, v)] -> k
minimumKey kvs = minimumBy (\x y -> compare (snd x) (snd y)) kvs

indexList :: [a] -> [(Int, a)]
indexList xs         = zip [1..(length xs)] xs





{-@ part        :: n:{v:Int | v > 0} -> [a] -> [{v:[a] | len(v) > 0}] @-}
part n []       = []
part n ys@(_:_) = zs : part n zs' 
                  where zs  = take n ys
                        zs' = drop n ys

-- | Recluster points
kmeans'' n clusters
  | clusters == clusters' = clusters
  | otherwise             = kmeans'' n clusters'
  where clusters'         = recluster n clusters

kmeans' n k points = kmeans'' n $ part l points
    where l = max 1 ((length points + k - 1) `div` k)

-- | Cluster points in a Euclidian space, represented as lists of Doubles, into at most k clusters.
-- The initial clusters are chosen arbitrarily.
{-@ kmeans :: n:Int 
           -> k:Int 
           -> points:[(Vec Double n)] 
           -> [[(Vec Double n)]] 
  @-}
kmeans :: Int -> Int -> [[Double]] -> [[[Double]]]
kmeans n = kmeansGen n id

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type 
--   which may be projected into a Euclidian space. Since the projection may be chosen freely, 
-- this allows for weighting dimensions to different degrees, etc.

{-@ kmeansGen :: n: Int -> f:(a -> (Vec Double n)) -> k:Int -> points:[a] -> [[a]] @-}
kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
kmeansGen n f k points = map (map getVal) . kmeans' n k . map (\x -> WrapType (f x) x) $ points


\end{code}



Conclusions
-----------

1. How to do *K-Means Clustering* !

2. Track precise length properties with **measures**

3. Circumvent limitations of SMT with a touch of **dynamic** checking using **assumes**


[vecbounds]:  /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:    https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:     http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[safeList]:   /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 



