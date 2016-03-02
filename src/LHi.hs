{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import           System.Environment      (getArgs)
import           System.Daemon
import           Control.Concurrent.MVar ( newMVar )
import           Data.Default ( def )
import           Language.Haskell.Liquid.Interactive.Types
import qualified Language.Haskell.Liquid.Interactive.Handler as H
import           Language.Haskell.Liquid.UX.CmdLine (getOpts)
import           Language.Haskell.Liquid.UX.Config  (port)

daemonName :: String
daemonName = "lhi0"

main :: IO ()
main = do
  st  <- newMVar H.initial
  cmd <- command
  ensureDaemonRunning daemonName (options cmd) (H.handler st)
  res <- client cmd
  print res

options :: Command -> DaemonOptions
options cmd = def { daemonPort = port cmd }

client :: Command -> IO (Maybe Response)
client cmd = runClient "localhost" (port cmd) cmd

---------------------------------------------------------------------------------
-- | Parsing Command Line -------------------------------------------------------
---------------------------------------------------------------------------------
command :: IO Command
-------------------------------------------------------------------------------
command = getOpts =<< getArgs
