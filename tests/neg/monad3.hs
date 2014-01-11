module Foo () where

import Language.Haskell.Liquid.Prelude

-- gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x >= 0) (x + 1)


-- decrlist n = n : decrlist (n-1)

xs, ys, zs :: [Int]
xs = [0, -1]
ys = gpp xs
zs = gpp ys
