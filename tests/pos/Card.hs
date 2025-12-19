{-@ LIQUID "--smtsolver=CVC5" @-}
module Card where

import Data.Set 
import qualified Data.Set as Set


{-@ insert :: x:Int -> xs:[Int] -> {v:[Int] | Set.size (Set.fromList v) >= Set.size (Set.fromList xs)} @-} 
insert :: Int -> [Int] -> [Int] 
insert x xs = x:xs



{-@ insert' :: x:Int -> xs:{[Int] | not (member x (fromList xs))} 
            -> {v:[Int] | Set.size (Set.fromList v) = 1 + Set.size (Set.fromList xs)} @-} 
insert' :: Int -> [Int] -> [Int] 
insert' x xs = x:xs