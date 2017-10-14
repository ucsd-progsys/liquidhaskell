{-@ LIQUID "--prune-unsorted" @-}

module Eval where


import qualified Data.Set as S

{-@ measure keys @-}
keys :: (Ord k) => [(k, v)] -> S.Set k
keys []       = S.empty
keys (kv:kvs) = (S.singleton (myfst kv)) `S.union` (keys kvs)

{-@ measure myfst @-}
myfst :: (a, b) -> a
myfst (x, _) = x

-- this is fine

{-@ measure okeys  :: [(a, b)] -> (S.Set a)
    okeys ([])     = (Set_empty 0)
    okeys (kv:kvs) = (Set_cup (Set_sng (fst kv)) (okeys kvs))
  @-}
