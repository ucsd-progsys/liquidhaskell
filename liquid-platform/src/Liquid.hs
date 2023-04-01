{-# LANGUAGE LambdaCase #-}

-- Calling LiquidHaskell via the source plugin
--
-- This executable is a wrapper around 'ghc', which gets passed an '-fplugin'
-- option. In addition, it hides all core libraries that might colide with a
-- package coming from liquid haskell.
--
-- The command line options of ghc and liquid haskell are merged together.
-- This script injects flags -fplugin-opt=LiquidHaskell:--opt for every
-- argument --opt intended for LiquidHaskell and occurring in the command line.

import Control.Monad

import System.Environment (lookupEnv, getArgs, unsetEnv)
import System.FilePath ((</>), takeDirectory, takeExtension)
import System.Process
import System.Exit
import Data.Char (toLower)
import Data.Maybe
import Data.Either (partitionEithers)
import Data.Bifunctor
import Data.Functor ((<&>))
import qualified System.Console.CmdArgs.Explicit as CmdArgs
import Data.List (partition, isPrefixOf, (\\))

import Language.Haskell.Liquid.UX.CmdLine (config, printLiquidHaskellBanner, getOpts)

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


helpNeeded :: [String] -> Bool
helpNeeded = elem "--help"

collectPackageDbsFromGHC_ENVIRONMENT :: IO [FilePath]
collectPackageDbsFromGHC_ENVIRONMENT = do
  lookupEnv "GHC_ENVIRONMENT" >>= \case
    Nothing -> return []
    Just envFile -> do
      contents <- readFile envFile
      return
        [ takeDirectory envFile </> drop (length pfx) xs
        | xs <- lines contents
        , let pfx = "package-db "
        , isPrefixOf pfx xs
        ]

main :: IO a
main = do

  -- If no args are passed, display the help instead of ghc's "no input files." To do so,
  -- due to the fact GHC needs to always have an input file to actually run a source plugin, we
  -- run this with '--interactive'.
  args <- getArgs <&> \case [] -> ["--interactive", "--help"]
                            xs -> "--make" : xs

  ghcPath <- fromMaybe "ghc" <$> lookupEnv "LIQUID_GHC_PATH"

  packageDbs <- collectPackageDbsFromGHC_ENVIRONMENT

  -- Strip targets out of the arguments, so that we can forward them to GHC before they
  -- get intercepted by the LH parser.
  let (targets, cliArgs)    =
        partition ((`elem` [".o", ".hs", ".lhs"]) . map toLower . takeExtension) args
  let (ghcArgs, liquidArgs) = partitionArgs cliArgs

  let p = proc ghcPath $
                         ["-package-env", "-"]
                         <> concat [ ["-package-db", p] | p <- packageDbs ]
                         <>
                         [ "-O0"
                         , "-no-link"
                         , "-fplugin=LiquidHaskell"
                         , "-plugin-package", "liquidhaskell"
                         , "-package", "liquid-containers"
                         , "-package", "liquid-prelude"
                         , "-package", "liquid-vector"
                         , "-package", "liquid-bytestring"
                         , "-hide-package", "containers"
                         , "-hide-package", "vector"
                         , "-hide-package", "bytestring"
                         , "-fplugin-opt=LiquidHaskell:--normal" -- normal logging.
                         ]
                         <> map (mappend "-fplugin-opt=LiquidHaskell:") liquidArgs
                         <> ghcArgs
                         <> targets

  -- Call into 'getOpts' so that things like the json reporter will correctly set the verbosity of the
  -- logging and avoid printing the banner.
  _ <- getOpts (args \\ ghcArgs)
  unless (helpNeeded args) printLiquidHaskellBanner

  -- Unset GHC_ENVIRONMENT so it doesn't influence ghc. Otherwise it would
  -- interfere when calling this program with cabal exec.
  unsetEnv "GHC_ENVIRONMENT"
  withCreateProcess p $ \_mbStdIn _mbStdOut _mbStdErr pHandle -> waitForProcess pHandle >>= exitWith
