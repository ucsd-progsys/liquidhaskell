module Dyn where

import Data.Dynamic 
import Data.Maybe

b0    = put 0 ("cat" :: String) 
      $ put 1 (12    :: Int) 
      $ emp

ok    = 10 `plus` (get 1 b0)

bad   = 10 `plus` (get 0 b0)

-------------------------------------------------
plus :: Int -> Int -> Int
plus = (+)

concat :: String -> String -> String
concat = (++)
-------------------------------------------------

type Field   = Int

newtype DBox = DB [(Field, Dynamic)]

emp :: DBox 
emp = DB []

put :: (Typeable a) => Field -> a -> DBox -> DBox 
put k v (DB b) = DB ((k, toDyn v) : b)

get :: (Typeable a) => Field -> DBox -> a 
get k (DB kvs) = ofD $ fromMaybe err $ lookup k kvs 
  where 
    err        = error $ "NOT FOUND" ++ show k

{-@ toD :: (Typeable a) => x:a -> {v:Dyn | (tag v) = (typeRep a)} @-}
toD :: (Typeable a) => a -> Dynamic 
toD = toDyn 

{-@ ofD :: {v:Dyn | (tag v) = (typeRep a)} -> a @-}
ofD :: (Typeable a) => Dynamic -> a
ofD = fromMaybe (error "DYNAMIC ERROR") . fromDynamic 
