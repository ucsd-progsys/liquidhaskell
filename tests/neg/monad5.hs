module Foo () where

import Language.Haskell.Liquid.Prelude

-- gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x > 0) (x + 1)

myabs :: Int -> Int
myabs x | x >= 0     = x
        | otherwise  = 0-x

posM :: Monad m => m Int
posM = return $ myabs $ choose 0


yM :: Monad m => m Int
yM = gpp posM
