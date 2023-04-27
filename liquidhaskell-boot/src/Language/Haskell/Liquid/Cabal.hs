{- | This module provides a drop-in replacement for Cabal's 'defaultMain', to be used inside 'Setup.hs'
     modules of packages that wants to use the \"dev mode\". For more information, visit the documentation,
     especially the \"Developers' guide\".
-}

{-# LANGUAGE LambdaCase #-}
module Language.Haskell.Liquid.Cabal (liquidHaskellMain) where

import Distribution.Simple
import System.Environment

liquidHaskellMain :: IO ()
liquidHaskellMain = do
  mbDevMode <- lookupEnv "LIQUID_DEV_MODE"
  defaultMainWithHooks (devModeHooks mbDevMode)

devModeHooks :: Maybe String -> UserHooks
devModeHooks = \case
  Nothing               -> simpleUserHooks
  Just x | x == "false" -> simpleUserHooks
  Just _                -> simpleUserHooks { buildHook = \_ _ _ _ -> return () }
