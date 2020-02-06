{-@ LIQUID "--typed-holes" @-}

module Map where 

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap = _map