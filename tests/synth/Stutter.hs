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


stutter x_s0 = 
    case x_s0 of 
        [] -> x_s0
        : x_s3 x_s4 -> _hole

    The goal is to fill the hole with:
    : x_s3 (: x_s3 (stutter x_s4))
-}