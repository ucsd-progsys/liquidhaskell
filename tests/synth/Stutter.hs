{-@ LIQUID "--typed-holes" @-}



{-@ stutter :: xs:[a] -> {v:[a] | 2 * len xs ==  len v} @-}
stutter :: [a] -> [a]
stutter = _stutter 


{-@ listId :: xs:[a] -> {v:[a] | len xs ==  len v} @-}
listId :: [a] -> [a]
listId = _listId 

{-
slutter [] = []
slutter (x:xs) = x:x:slutter xs 


-}