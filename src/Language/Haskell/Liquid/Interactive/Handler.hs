module Language.Haskell.Liquid.Interactive.Handler (
    -- * Initial state for server
    initial

    -- * Command handler
  , handler
  ) where

import Control.Concurrent.MVar
import Data.HashMap.Strict as M
import Language.Haskell.Liquid.Interactive.Types
import Language.Haskell.Liquid.Liquid

------------------------------------------------------------------------------
handler :: MVar State -> Command -> IO Response
------------------------------------------------------------------------------
handler r cfg = do
  n  <- sCount <$> readMVar r
  putStrLn $ "LHi query " ++ show n
  response <$> runLiquid cfg

------------------------------------------------------------------------------
initial :: State
------------------------------------------------------------------------------
initial = State 0
