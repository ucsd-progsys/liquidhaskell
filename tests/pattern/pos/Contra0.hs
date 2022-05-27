{-@ LIQUID "--no-termination"    @-}
{-@ LIQUID "--short-names"       @-}

module Contra0 () where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Data.IORef


{-@ data variance IO bivariant @-}
{-@ data variance IORef bivariant @-}

job :: IO () 
job = do
  p <- newIORef (0 :: Int)
  writeIORef p 10
  v <- readIORef p
  liquidAssert (v >= 0) $ return ()
