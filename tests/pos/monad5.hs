module Foo where

import Language.Haskell.Liquid.Prelude

-- gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x > 0) (x + 1)

posM :: Monad m => m Int
posM = return 9


yM :: Monad m => m Int
yM = gpp posM
