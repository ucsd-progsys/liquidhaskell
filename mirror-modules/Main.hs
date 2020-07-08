
module Main where

import           CLI
import           Options.Applicative

import qualified Data.Text                               as T
import qualified Data.Text.IO                            as TIO
import qualified Data.Set                                as S
import           Data.Set                                 ( Set )
import           Data.Function                            ( (&) )

import           System.FilePath
import           Shelly                                  as Sh

--
-- Utility functions
--

findExistingModules :: CLI -> Sh (Set T.Text)
findExistingModules cli = do
  allFiles <- Sh.findWhen (\f -> pure $ takeExtension f == ".hs") (moduleHierarchyRoot cli)
  pure . S.fromList . map transform $ allFiles
  where
    -- Transform an input file by:
    -- * Stripping the path;
    -- * Replacing slashes with dots;
    -- * Remove the final \".hs"\ extension.
    transform :: FilePath -> T.Text
    transform f = f & dropExtension
                    & T.pack
                    & T.replace (T.pack $ moduleHierarchyRoot cli) mempty
                    & T.replace "/" "."
                    & T.replace "/" "."

-- Extracts the name of the mirrored package by dropping the \"liquid-\" prefix.
mirroredPackage :: CLI -> T.Text
mirroredPackage = T.tail . snd . T.breakOn "-" . mirrorPackageName

--
-- The main workhorse
--

mirrorModules :: CLI -> IO ()
mirrorModules cli@CLI{..} = shelly $ do
  inputModules    <- S.fromList . map T.strip . T.words <$> liftIO (TIO.readFile modulesList)
  existingModules <- findExistingModules cli
  let notMirrored = inputModules `S.difference` existingModules
  echo $ (T.pack . show $ notMirrored)

main :: IO ()
main = mirrorModules =<< execParser opts
  where
    opts = info (parseCLI <**> helper)
      ( fullDesc
     <> progDesc "Create modules to be used in mirror packages."
     <> header "mirror-modules - Generate modules in mirror packages." )
