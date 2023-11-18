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
import System.FilePath ((</>), takeDirectory)
import System.Process
import System.Exit
import Data.Maybe
import Data.Bifunctor
import Data.List (isPrefixOf, (\\))

import Language.Haskell.Liquid.UX.CmdLine (printLiquidHaskellBanner, getOpts)

type GhcArg    = String
type LiquidArg = String

partitionArgs :: [String] -> ([GhcArg], [LiquidArg])
partitionArgs = second (drop 1) . break ("--"==)

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
  args0 <- getArgs
  when (null args0 || elem "--help" args0) $
    putStr $ unlines
      [ "Usage:"
      , ""
      , "    liquidhaskell <ghc arguments> [-- <Liquid Haskell arguments>]"
      , ""
      ]
  let args = case args0 of
               [] -> ["--interactive", "--", "--help"]
               xs -> "--make" : xs

  ghcPath <- fromMaybe "ghc" <$> lookupEnv "LIQUID_GHC_PATH"

  packageDbs <- collectPackageDbsFromGHC_ENVIRONMENT

  let (ghcArgs, liquidArgs) = partitionArgs args

  let p = proc ghcPath $
                         ["-package-env", "-"]
                         <> concat [ ["-package-db", p] | p <- packageDbs ]
                         <>
                         [ "-O0"
                         , "-no-link"
                         , "-fplugin=LiquidHaskell"
                         , "-plugin-package", "liquidhaskell"
                         , "-fplugin-opt=LiquidHaskell:--normal" -- normal logging.
                         ]
                         <> map (mappend "-fplugin-opt=LiquidHaskell:") liquidArgs
                         <> ghcArgs

  -- Call into 'getOpts' so that things like the json reporter will correctly set the verbosity of the
  -- logging and avoid printing the banner.
  _ <- getOpts (args \\ ghcArgs)
  unless (helpNeeded args) printLiquidHaskellBanner

  -- Unset GHC_ENVIRONMENT so it doesn't influence ghc. Otherwise it would
  -- interfere when calling this program with cabal exec.
  unsetEnv "GHC_ENVIRONMENT"
  withCreateProcess p $ \_mbStdIn _mbStdOut _mbStdErr pHandle -> waitForProcess pHandle >>= exitWith
