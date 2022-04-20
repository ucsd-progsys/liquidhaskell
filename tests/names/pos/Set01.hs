-- TEST that the name `member` is properly resolved to Set_mem. 
-- TAG: LOGICMAP 

module Set01 where

import Data.Set as S

{-@ add :: x:a -> [a] -> {v:[a] | member x (listElts v)} @-}
add :: a -> [a] -> [a]
add x xs = x : xs 

