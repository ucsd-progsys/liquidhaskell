module Language.Haskell.Liquid.Interactive.Handler (
    -- * Initial state for server
    initial

    -- * Command handler
  , handler
  ) where

import Prelude hiding (error)
import Control.Concurrent.MVar
import Language.Haskell.Liquid.Interactive.Types
import Language.Haskell.Liquid.Liquid

------------------------------------------------------------------------------
handler :: MVar State -> Command -> IO Response
------------------------------------------------------------------------------
handler r = modifyMVar r . runLiquid'

runLiquid' :: Command -> State -> IO (State, Response)
runLiquid' cfg s = do
  let mE    = sMbEnv s
  let n     = sCount s
  (c, mE') <- runLiquid mE cfg
  let s'    = State (n + 1) mE'
  return      (s', (status c, n))

------------------------------------------------------------------------------
initial :: State
------------------------------------------------------------------------------
initial = State 0 Nothing
