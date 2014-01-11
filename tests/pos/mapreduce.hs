module Meas () where

import Language.Haskell.Liquid.Prelude
import qualified Data.Map
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

group   :: (Ord k) => [(k, v)] -> Data.Map.Map k [v]
group   = foldl' addKV  Data.Map.empty
  
addKV m (k, v) = Data.Map.insert k vs' m
  where 
    vs' = v : (Data.Map.findWithDefault [] k m)

--------------------------------------------------------------------
--- Step 3: Group By Key -------------------------------------------
--------------------------------------------------------------------

collapse f                = Data.Map.foldrWithKey reduceKV []
  where 
    reduceKV k (v:vs) acc = let b = liquidAssertB False in (k, foldl' f v vs) : acc
    reduceKV k []     _   = crash False --error $ show (liquidAssertB False)

--------------------------------------------------------------------
--- Putting it All Together ----------------------------------------
--------------------------------------------------------------------

mapReduce mapper reducer = collapse reducer . group . expand mapper 

--------------------------------------------------------------------
--- "Word Count" ---------------------------------------------------
--------------------------------------------------------------------

wordCount  = mapReduce fm plus 
  where fm = \doc -> [ (w,1) | w <- words doc]

main = putStrLn $ show $ wordCount docs
  where docs = [ "this is the end"
               , "go to the end"
               , "the end is the beginning"]
 

