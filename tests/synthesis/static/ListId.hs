{-@ LIQUID "--typed-holes" @-}

import Language.Haskell.Liquid.Synthesize.Error

{-@ listId :: xs:[a] -> {v:[a] | len xs ==  len v} @-}
listId :: [a] -> [a]
listId x_S0 = x_S0
