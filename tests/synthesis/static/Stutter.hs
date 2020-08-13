{-@ LIQUID "--typed-holes" @-}

import Language.Haskell.Liquid.Synthesize.Error


{-@ stutter :: xs:[a] -> {v:[a] | 2 * len xs ==  len v} @-}
stutter :: [a] -> [a]
stutter x_S0 =
    case x_S0 of
        [] -> []
        (:) x_Sa x_Sb -> (:) x_Sa ((:) x_Sa (stutter x_Sb))