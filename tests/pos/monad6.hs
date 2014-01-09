module Foo () where

import Language.Haskell.Liquid.Prelude 

{-@ gpp :: Monad m => m {v:Int|v>=0} -> m {v:Int|v>=0} @-}
gpp :: Monad m => m Int -> m Int
gpp z = do x <- z
           return $ liquidAssert (x >= 0) (x + 1)


xM :: [Int]
xM = gpp [0]
