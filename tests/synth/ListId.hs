{-@ LIQUID "--typed-holes" @-}

{-@ listId :: xs:[a] -> {v:[a] | len xs ==  len v} @-}
listId :: [a] -> [a]
listId = _listId 
