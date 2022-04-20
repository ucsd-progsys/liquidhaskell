{- LIQUID "--pruneunsorted" @-}

module ListKeys () where
import Data.Set (Set(..), empty, union, singleton) 

{-@  measure listKeys @-}
listKeys :: Ord k => [(k, v)] -> Set k 
listKeys [] = empty 
listKeys (x:xs) = singleton (myfst x) `union` listKeys xs 

{-@ measure myfst @-}
myfst :: (a,b) -> a 
myfst (x,_) = x 

{-@ getFsts :: ys:[(a, b)] -> {v : [a] | listElts v = listKeys ys } @-}
getFsts ::[(a, b)] ->  [a]
getFsts []           = []
getFsts ((x, _): xs) = x : getFsts xs






