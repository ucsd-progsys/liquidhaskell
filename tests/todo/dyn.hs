module Dyn where

b0 = put 0 ("cat" :: String) 
   $ put 1 (12    :: Int) 
   $ empty

z  = plus 10 (get 1 b0)

plus :: Int -> Int -> Int
plus = (+)

concat :: String -> String -> String
concat = (++)

type Field   = Int
data Dyn

newtype DBox = DB [(Field, Dyn)]

emp :: DBox 
emp = DB []

put :: Field -> a -> DBox -> DBox 
put k v b = (k, toDyn v) : b

get :: Field -> DBox -> a 
get k (DB kvs) = ofDyn $ maybe err $ lookup k kvs 
  where 
    err        = error $ "NOT FOUND" ++ show k

-- toDyn :: x:a -> {v:Dyn | (tag v) = (ty a)}
toDyn :: a -> Dyn 
toDyn = unsafeCoerce

-- ofDyn :: {v:Dyn | (tag v) = (ty a)} -> a 
ofDyn :: Dyn -> a
ofDyn = unsafeCoerce
