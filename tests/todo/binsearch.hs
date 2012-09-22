module BinSearch where

import Language.Haskell.Liquid.Prelude
import Data.Vector

foobar = div

gobble n lo hi 
  | hi < lo   = True 
  | otherwise = let mid = (hi - lo) `div` 2 
                in assert (mid >= 0)

z = gobble n 0 n
    where n = choose 0


--binarySearch :: (Ord a) => Vector a -> a -> Int -> Int -> Maybe Int
--binarySearch haystack needle lo hi
--  | hi < lo	        = Nothing
--  | pivot > needle	= binarySearch haystack needle lo (mid - 1)
--  | pivot < needle	= binarySearch haystack needle (mid + 1) hi
--  | otherwise	    = Just mid
--  where mid	    = lo + ((hi - lo) `div` 2)
--        pivot	= haystack ! mid
--
--runBinarySearch haystack needle 
--  = binarySearch haystack needle 0 (Data.Vector.length haystack)
--
--pos = runBinarySearch vec val
--  where vec = fromList [0..siz]
--        siz = choose 0
--        val = choose 1
