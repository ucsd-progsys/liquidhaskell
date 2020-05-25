{-@ LIQUID "--typed-holes" @-}

module ListZipWith where

import Language.Haskell.Liquid.Synthesize.Error

{-@ zipWith' :: f: (a -> b -> c) 
               -> xs: [a] 
               -> { ys: [b] | len ys == len xs} 
               -> {v: [c] | len v == len xs } 
@-}
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' x_S0 x_S1 x_S2 =
    case x_S1 of
        [] -> []
        (:) x_St x_Su ->
            case x_S2 of
                [] -> error " Dead code! "
                (:) x_S1d x_S1e -> (:) (x_S0 x_St x_S1d) (zipWith' x_S0 x_Su x_S1e)