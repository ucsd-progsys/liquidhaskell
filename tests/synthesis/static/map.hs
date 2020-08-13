{-@ LIQUID "--typed-holes" @-}

module Map where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap x_S0 x_S1 =
    case x_S1 of
        [] -> []
        (:) x_Sf x_Sg -> (:) (x_S0 x_Sf) (myMap x_S0 x_Sg)