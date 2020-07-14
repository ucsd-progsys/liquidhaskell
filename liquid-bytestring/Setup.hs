module Main where

import Distribution.Simple
import System.Environment

main :: IO ()
main = do
  libHooks <- customHooks
  defaultMainWithHooks libHooks

customHooks :: IO UserHooks
customHooks = do
  mbDevMode <- lookupEnv "LIQUID_DEV_MODE"
  case mbDevMode of
    Nothing -> pure simpleUserHooks
    Just x  -> pure simpleUserHooks { buildHook = \_ _ _ _ -> return () }
