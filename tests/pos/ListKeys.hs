{-@ LIQUID "--pruneunsorted" @-}

module Foo () where
import Data.Set (Set(..)) 

{-@  measure listKeys :: [(k, v)] -> (Set k) 
    listKeys([])   = {v | Set_emp v }
    listKeys(x:xs) = {v | v = (Set_cup (Set_sng (fst x)) (listKeys xs)) }

@-}


{-@ getFsts :: ys:[(a, b)] -> {v : [a] | listElts v = listKeys ys } @-}
getFsts ::[(a, b)] ->  [a]
getFsts []           = []
getFsts ((x, _): xs) = x : getFsts xs






