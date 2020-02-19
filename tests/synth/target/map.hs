{-@ LIQUID "--typed-holes" @-}

module Map where 

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap = _map