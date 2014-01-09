module Meas () where

import Language.Haskell.Liquid.Prelude
import Data.List (foldl')

mylen          :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs

----------------------------------------------------------------
--- Step 1: Map each element into key-value list (concatMap) ---
----------------------------------------------------------------

expand          :: (a -> [(k,v)]) -> [a] -> [(k, v)]
expand f []     = []
expand f (x:xs) = (f x) ++ (expand f xs)

----------------------------------------------------------------
--- Step 2: Group By Key ---------------------------------------
----------------------------------------------------------------

group ::[(Int, v)] -> [(Int, [v])]
group = foldl' addKV [] 
  
addKV m (k, v) = insert k vs' m
  where vs' = v : (findWithDefault [] k m)

insert key value [] 
  = [(key, value)]
insert key value ((k,_):kvs)
  | k == key
  = (key, value):kvs
insert key value (kv:kvs)
  = kv : insert key value kvs  

{-@ Decrease findWithDefault 3 @-}
findWithDefault r _ ([]) 
  = r
findWithDefault r k ((key,value):_) 
  | k `eq` key 
  = value
findWithDefault r k (_:kvs) 
  = findWithDefault r k kvs 

----------------------------------------------------------------
--- Step 3: Group By Key ---------------------------------------
----------------------------------------------------------------

collapse f = foldrWithKey reduceKV []
  where reduceKV k (v:vs) acc = (k, foldl' f v vs) : acc
        reduceKV k []     _   = crash False -- error $ show (liquidAssertB False)

foldrWithKey f = foldr (\(k, v) acc -> f k v acc) 

----------------------------------------------------------------
--- Putting it All Together ------------------------------------
----------------------------------------------------------------

mapReduce fmap fred xs = collapse fred $ group $ expand fmap xs

----------------------------------------------------------------
--- "Word Count" -----------------------------------------------
----------------------------------------------------------------

wordCount  = mapReduce fm plus 
  where fm = \doc -> [ (length w, 1) | w <- words doc]

mytest = 
  let docs = [ "this is the end"
             , "go to the end"
             , "the end is the beginning"]
  in putStrLn $ isZero {- show -} $ wordCount docs
 
isZero [_]  = "Positive" 
isZero _    = "Negative"

