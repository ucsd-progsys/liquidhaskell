{-@ LIQUID "--typed-holes" @-}

module ListZip where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ zip' :: xs: [a] -> {ys:[b] | len ys == len xs} -> {v:[(a, b)] | len v == len xs} @-}
zip' :: [a] -> [b] -> [(a, b)]
zip' x_S0 x_S1 =
    case x_S0 of
        [] -> [], b)
        (:) x_Sl x_Sm ->
            case x_S1 of
                [] -> error " Dead code! "
                (:) x_S14 x_S15 -> (:), b) (x_Sl, x_S14) (zip' x_Sm x_S15)