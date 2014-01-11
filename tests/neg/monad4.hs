module Foo () where

import Language.Haskell.Liquid.Prelude

-- gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x > 0) (x - 10)


incrlist n = n : incrlist (n+1)

xs, ys, zs :: Maybe Int
xs = Just 9
ys = gpp xs
zs = gpp ys
