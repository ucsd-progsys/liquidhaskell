-- | This program calls ghc using the provided command line arguments.
-- Use it to profile the liquidhaskell plugin.
--
-- Build liquidhaskell and this program with profiling enabled.
--
-- > cabal build --enable-profiling liquidhaskell profiling-driver
--
-- Add the plugin as an option pragma to the file on which the plugin should run.
--
-- > echo "{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}" > tests/basic/pos/Inc02.hs
--
-- Then run this program with
--
-- > cabal exec --enable-profiling -- profiling-driver +RTS -p -RTS tests/basic/pos/Inc02.hs
--
-- This will generate a file profiling-driver.prof with the profiling results.
--
-- Ideally, passing @-fplugin=LiquidHaskell@ on the command line should have the
-- same effect as adding the plugin as an option pragma to the file, but for
-- some reason it didn't work the last time we tried.
module Main where

import GHC as G

import Control.Monad
import Control.Monad.IO.Class
import System.Environment
import GHC.Paths (libdir)
import GHC.Utils.Logger as G

main :: IO ()
main = do
    xs <- getArgs
    runGhc (Just libdir) $ do
      df1 <- getSessionDynFlags
      let cmdOpts = ["-fforce-recomp"] ++ filter ("--make" /=) xs
      logger <- liftIO G.initLogger
      (df2, leftovers, _warns) <- G.parseDynamicFlags logger df1 (map G.noLoc cmdOpts)
      setSessionDynFlags df2
      ts <- mapM (\x-> G.guessTarget x Nothing Nothing) $ map unLoc leftovers
      setTargets ts
      void $ G.load LoadAllTargets
