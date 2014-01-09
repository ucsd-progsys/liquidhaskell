
-- RJ: Issues with TypeClasses? Ord?

module Meas () where

import Language.Haskell.Liquid.Prelude
import qualified Data.Map as M
import Data.List (foldl')

----------------------------------------------------------------
--- Step 1: Map each element into key-value list (concatMap) ---
----------------------------------------------------------------

expand          :: (a -> [(k,v)]) -> [a] -> [(k, v)]
expand f []     = []
expand f (x:xs) = (f x) ++ (expand f xs)

----------------------------------------------------------------
--- Step 2: Group By Key ---------------------------------------
----------------------------------------------------------------

group :: (Ord k) => [(k, v)] -> M.Map k [v]
group = foldl' addKV  M.empty
  
addKV m (k, v) = M.insert k vs' m
  where vs' = v : (M.findWithDefault [] k m)

----------------------------------------------------------------
--- Step 3: Group By Key ---------------------------------------
----------------------------------------------------------------

collapse f = M.foldrWithKey reduceKV []
  where reduceKV k (v:vs) acc = if liquidAssertB False then (k, foldl' f v vs) : acc else acc
        reduceKV k []     _   = crash False --error $ show (liquidAssertB False)

----------------------------------------------------------------
--- Putting it All Together ------------------------------------
----------------------------------------------------------------

mapReduce fmap fred = collapse fred . group . expand fmap 

----------------------------------------------------------------
--- "Word Count" -----------------------------------------------
----------------------------------------------------------------

wordCount  = mapReduce fm plus 
  where fm = \doc -> [ (w,1) | w <- words doc]

main = putStrLn $ show $ wordCount docs
  where docs = [ "this is the end"
               , "go to the end"
               , "the end is the beginning"]
 


