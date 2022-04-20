module T1396_0 where

data Map k
  = Leaf
  | Node k (Map k)

foo :: (Ord k) => Map k -> k -> ()
foo (Node k l) key
  | key == k  = ()
  | otherwise = foo l key
foo Leaf _ = ()
