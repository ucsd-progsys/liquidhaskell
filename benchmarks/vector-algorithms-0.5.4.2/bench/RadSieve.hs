-- ------------------------------------------------------------------
--
-- Module        : RadSieve
-- Copyright     : (c) 2009 Dan Doel
--
-- ------------------------------------------------------------------
-- An implementation of a radical sieve, inspired by solving Project
-- Euler problem #124.
--
-- Reproduction fo the problem text:
--
-- The radical of n, rad(n), is the product of distinct prime factors
-- of n. For example, 504 = 23 × 32 × 7, so rad(504) = 2 × 3 × 7 = 42.
--
-- If we calculate rad(n) for 1 ≤ n ≤ 10, then sort them on rad(n),
-- and sorting on n if the radical values are equal, we get:
--
--   Unsorted                 Sorted
--   n  rad(n)             n  rad(n)  k
--   1    1                1    1     1
--   2    2                2    2     2
--   3    3                4    2     3
--   4    2                8    2     4
--   5    5                3    3     5
--   6    6                9    3     6
--   7    7                5    5     7
--   8    2                6    6     8
--   9    3                7    7     9
--  10   10               10   10    10
--
-- Let E(k) be the kth element in the sorted n column; for example,
-- E(4) = 8 and E(6) = 9.
--
-- If rad(n) is sorted for 1 ≤ n ≤ 100000, find E(10000).

module RadSieve where

import Control.Monad
import Control.Monad.ST

import Data.Array.Vector

-- Radicals can be sieved as follows:
--   set a[1,n] = 1
--   for i from 2 to n
--     if a[i] == 1     -- i must be prime
--      then a[j*i] *= i for positive integers j, j*i <= n
--      else do nothing -- i is composite, so its prime factors
--                      -- have been accounted for
--
-- This sieves for radicals up to the given integer.
radSieve :: Int -> ST s (MUArr Int s)
radSieve n = do arr <- newMU (n + 1)
                fill arr n
                sieve arr 1
                return arr
 where
 fill arr i   | i < 0     = return ()
              | otherwise = writeMU arr i 1 >> fill arr (i-1)
 sieve arr i  | n < i     = return ()
              | otherwise = do e <- readMU arr i
                               when (e == 1) $ mark arr i i
                               sieve arr (i+1)
 mark arr p j | n < j     = return ()
              | otherwise =  readMU arr j >>= writeMU arr j . (*p)
                          >> mark arr p (j+p)

-- Computes the answer to the above Project Euler problem. The correct
-- answer is only generated for a stable sorting function.
stableSortedRad :: Int -> Int
                -> (forall s e. UA e => Comparison e -> MUArr e s -> ST s ()) 
                -> Int
stableSortedRad n k sortBy = runST (do rads <- radSieve n
                                       index <- newMU (n + 1)
                                       fillUp index n
                                       sortBy (comparing fstS)
                                              (unsafeZipMU rads index)
                                       readMU k index)
 where
 fillUp arr k | k < 0     = return ()
              | otherwise = writeMU arr k k >> fillUp arr (k-1)

-- Computes the answer to the above Project Euler problem. This version
-- will generate the correct answer even for unstable sorts, but may be
-- marginally slower.
unstableSortedRad :: Int -> Int
                  -> (forall s e. UA e => Comparison e -> MUArr e s -> ST s ()) 
                  -> Int
unstableSortedRad n k sortBy = runST (do rads <- radSieve n
                                       index <- newMU (n + 1)
                                       fillUp index n
                                       sortBy compare (unsafeZipMU rads index)
                                       readMU k index)
 where
 fillUp arr k | k < 0     = return ()
              | otherwise = writeMU arr k k >> fillUp arr (k-1)

