{-@ LIQUID "--typed-holes" @-}

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

{-@ listId :: xs:[a] -> {v:[a] | len xs ==  len v} @-}
listId :: [a] -> [a]
listId = _listId 
