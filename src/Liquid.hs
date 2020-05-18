
{-| Calling LiquidHaskell via the source plugin.
  This executable is a simple wrapper around 'ghc', which will be called with LiquidHaskell source plugin.
-}

import System.Environment (lookupEnv, getArgs)
import System.Process
import System.Exit
import Data.Maybe

main :: IO a
main = do
  args <- getArgs
  ghcPath <- fromMaybe "ghc" <$> lookupEnv "LIQUID_GHC_PATH"

  let p = proc ghcPath $ [ "-O0"
                         , "--make"
                         , "-no-link"
                         , "-fplugin=Language.Haskell.Liquid.GHC.Plugin"
                         , "-plugin-package", "liquidhaskell"
                         , "-package", "liquid-base"
                         , "-hide-package", "base"
                         ] <> args

  withCreateProcess p $ \_mbStdIn _mbStdOut _mbStdErr pHandle -> waitForProcess pHandle >>= exitWith
