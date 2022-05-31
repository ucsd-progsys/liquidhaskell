{-@ LIQUID "--expect-any-error" @-}
-- TEST that the name `member` is properly resolved to Set_mem. 
-- TAG: LOGICMAP 

module Set00 where 

import Data.Set as S

{-@ add :: x:a -> [a] -> {v:[a] | Set_mem x (listElts v)} @-}
add :: a -> [a] -> [a]
add x xs = xs 

