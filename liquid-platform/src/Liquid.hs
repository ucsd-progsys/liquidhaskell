
{-| Calling LiquidHaskell via the source plugin.
  This executable is a simple wrapper around 'ghc', which gets passed an '-fplugin' option.
-}

import System.Environment (lookupEnv, getArgs)
import System.Process
import System.Exit
import Data.Maybe
import Data.List (partition, isPrefixOf)

main :: IO a
main = do
  args <- getArgs
  ghcPath <- fromMaybe "ghc" <$> lookupEnv "LIQUID_GHC_PATH"

  let (cliArgs, targets) = partition ("-" `isPrefixOf`) args

  let p = proc ghcPath $ [ "-O0"
                         , "--make"
                         , "-no-link"
                         , "-fplugin=Language.Haskell.Liquid.GHC.Plugin"
                         , "-plugin-package", "liquidhaskell"
                         , "-package", "liquid-base"
                         , "-hide-package", "base"
                         ] 
                         <> targets 
                         <> map (mappend "-fplugin-opt=Language.Haskell.Liquid.GHC.Plugin:") cliArgs

  withCreateProcess p $ \_mbStdIn _mbStdOut _mbStdErr pHandle -> waitForProcess pHandle >>= exitWith
