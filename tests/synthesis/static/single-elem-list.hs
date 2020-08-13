{-@ LIQUID "--typed-holes" @-}

import Language.Haskell.Liquid.Synthesize.Error

-- This is to test `nilDataCons`.
{-@ oneElem :: xs:a -> {v:[a] | len v == 1} @-}
oneElem :: a -> [a]
oneElem x_S0 = (:) x_S0 []
