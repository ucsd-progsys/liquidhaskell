module Language.Haskell.Liquid.Interactive.Handler (
    -- * Initial state for server
    initial

    -- * Command handler
  , handler
  ) where

import Control.Concurrent.MVar
-- import Data.HashMap.Strict as M
import Language.Haskell.Liquid.Interactive.Types
import Language.Haskell.Liquid.Liquid

------------------------------------------------------------------------------
handler :: MVar State -> Command -> IO Response
------------------------------------------------------------------------------
handler r cfg = do
  n <- yo r
  s <- status <$> runLiquid cfg
  return (s, n)

-- | What up
yo :: MVar State -> IO Int
yo r = do
  n <- bump r
  writeFile "/Users/rjhala/tmp/lhi.log" (msg n)
  return n

msg n = "Lhi: Query " ++ show n

bump :: MVar State -> IO Int
bump r = modifyMVar r $ \s ->
  let n = sCount s in
  return (s { sCount = n + 1 },  n)

------------------------------------------------------------------------------
initial :: State
------------------------------------------------------------------------------
initial = State 0
