{-@ LIQUID "--exactdc" @-}

import Prelude hiding (replicate)

{-@ reflect replicate @-}
replicate :: Int -> a -> [a]
replicate 0 _ = []
replicate n x = x:(replicate (n - 1) x)

