
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1245

module T1245 where

import qualified Data.Set as S 


{-@ data Map [size] @-}
data Map k v =
    Empty
  | Bind k v (Map k v)

{-@ measure size @-}
{-@ size :: Map k v -> Nat @-}
size :: Map k v -> Int
size Empty = 0
size (Bind _ _ r) = 1 + size r

{-@ measure keys @-}
{-@ keys :: zzz: Map k v -> S.Set k / [size zzz, 0] @-}
keys :: Ord k => Map k v -> S.Set k
keys Empty = S.empty
keys (Bind k _ r) = add k r

{-@ inline add @-}
{-@ add :: k -> zzz:Map k v -> S.Set k / [size zzz, 1] @-}
add :: Ord k => k -> Map k v -> S.Set k
add k r = S.singleton k `S.union` keys r


