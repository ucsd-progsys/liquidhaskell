{-# LANGUAGE LambdaCase #-}

{-| Calling LiquidHaskell via the source plugin.
  This executable is a simple wrapper around 'ghc', which gets passed an '-fplugin' option.
-}

import System.Environment (lookupEnv, getArgs)
import System.Process
import System.Exit
import Data.Maybe
import Data.Either (partitionEithers)
import Data.Bifunctor
import Data.Functor ((<&>))
import qualified System.Console.CmdArgs.Explicit as CmdArgs
import Data.List (partition, isPrefixOf)

import Language.Haskell.Liquid.UX.CmdLine (config)

type GhcArg    = String
type LiquidArg = String

partitionArgs :: [String] -> ([GhcArg], [LiquidArg])
partitionArgs args = partitionEithers (map parseArg args)
  where
    parseArg :: String -> Either GhcArg LiquidArg
    parseArg a 
      | forwardToGhc a = Left a
      | otherwise      = bimap (const a) (const a) (CmdArgs.process config [a])

    -- Unfortunate consequence of the facts things like '-i' needs to be forwarded to GHC
    -- and not the LH executable.
    forwardToGhc :: String -> Bool
    forwardToGhc = isPrefixOf "-i"

main :: IO a
main = do

  -- If no args are passed, display the help instead of ghc's "no input files." To do so,
  -- due to the fact GHC needs to always have an input file to actually run a source plugin, we
  -- run this with '--interactive'.
  args <- getArgs <&> \case [] -> ["--interactive", "--help"]
                            xs -> "--make" : xs

  ghcPath <- fromMaybe "ghc" <$> lookupEnv "LIQUID_GHC_PATH"

  -- Strip targets out of the arguments, so that we can forward them to GHC before they
  -- get intercepted by the LH parser.
  let (cliArgs, targets)    = partition (isPrefixOf "-") args
  let (ghcArgs, liquidArgs) = partitionArgs cliArgs

  let p = proc ghcPath $ [ "-O0"
                         , "-no-link"
                         , "-fforce-recomp"
                         , "-fplugin=Language.Haskell.Liquid.GHC.Plugin"
                         , "-plugin-package", "liquidhaskell"
                         , "-package", "liquid-ghc-prim"
                         , "-package", "liquid-base"
                         , "-package", "liquid-containers"
                         , "-package", "liquid-prelude"
                         , "-package", "liquid-vector"
                         , "-package", "liquid-bytestring"
                         , "-hide-package", "ghc-prim"
                         , "-hide-package", "base"
                         , "-hide-package", "containers"
                         , "-hide-package", "vector"
                         , "-hide-package", "bytestring"
                         ]
                         <> map (mappend "-fplugin-opt=Language.Haskell.Liquid.GHC.Plugin:") liquidArgs
                         <> ghcArgs
                         <> targets

  withCreateProcess p $ \_mbStdIn _mbStdOut _mbStdErr pHandle -> waitForProcess pHandle >>= exitWith
