module Vec0 where

import qualified Data.Vector as V 

propVec = (vs V.! 3) == 3
  where xs    = [1,2,3,4] :: [Int]
        vs    = V.fromList xs
        
{-@ unsafeLookup :: V.Vector a -> Int -> a @-}
unsafeLookup x i = x V.! i

{-@ safeLookup :: V.Vector a -> Int -> Maybe a @-}
safeLookup x i 
  | 0 <= i && i < V.length x = Just (x V.! i)
  | otherwise                = Nothing 
