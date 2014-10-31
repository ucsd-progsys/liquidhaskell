{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Foo () where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Data.IORef

{-@ job :: IO () @-}
job = do
  p <- newIORef (0 :: Int)
  writeIORef p 10
  v <- readIORef p
  liquidAssert (v == 0) $ return ()
