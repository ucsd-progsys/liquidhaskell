module Eval where

import qualified Data.Set as S

{-@ measure keys @-}
keys :: (Ord k) => [(k, v)] -> S.Set k
keys []       = S.empty
keys (kv:kvs) = (S.singleton (fst kv)) `S.union` (keys kvs)

