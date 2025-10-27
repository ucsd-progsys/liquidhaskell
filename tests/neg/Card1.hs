{-@ LIQUID "--expect-any-error" @-}
{- LIQUID "--smtsolver=CVC5" @-}
-- Z3 does not support cardinality of sets
module Card1 where

import Data.Set 
import qualified Data.Set as Set


{-@ insert :: x:Int -> xs:[Int] -> {v:[Int] | Set.size (Set.fromList v) >= Set.size (Set.fromList xs)} @-} 
insert :: Int -> [Int] -> [Int] 
insert x xs = x:xs