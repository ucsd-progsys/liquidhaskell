module Foo () where

import Language.Haskell.Liquid.Prelude

-- gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x >= 0) (x + 1)

gpp' z n = do x <- z n
              return $ liquidAssert (x >= 0) (x + 1)


myabs :: Int -> Int
myabs x | x >= 0     = x
        | otherwise  = 0-x

myabsM :: Monad m => Int -> m Int
myabsM x | x >= 0     = return $ x
         | otherwise  = return $ 0-x


posM :: Monad m => m Int
posM = return $ myabs $ choose 0


xM, yM :: Monad m => m Int
yM = gpp posM
xM = gpp' myabsM $ choose 0
