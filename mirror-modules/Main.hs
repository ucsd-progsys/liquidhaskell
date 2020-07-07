
module Main where

import CLI
import Options.Applicative
import qualified Data.Text as T

import System.FilePath

import Shelly as Sh


main :: IO ()
main = mirrorModules =<< execParser opts
  where
    opts = info (parseCLI <**> helper)
      ( fullDesc
     <> progDesc "Create modules to be used in mirror packages."
     <> header "mirror-modules - Generate modules in mirror packages." )


mirrorModules :: CLI -> IO ()
mirrorModules cli = shelly (findExistingModules cli) >>= print


findExistingModules :: CLI -> Sh [T.Text]
findExistingModules cli = do
  allFiles <- Sh.findWhen (\f -> pure $ takeExtension f == ".hs") (moduleHierarchyRoot cli)
  pure $ map (T.replace "/" "." . T.replace (T.pack $ moduleHierarchyRoot cli) mempty . T.pack) allFiles
