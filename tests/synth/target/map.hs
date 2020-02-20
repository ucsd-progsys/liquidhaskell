{-@ LIQUID "--typed-holes" @-}

module Map where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap = _map