
module Main where

import           CLI
import           Options.Applicative

import           Control.Monad

import qualified Data.Text                               as T
import qualified Data.Set                                as S
import qualified Data.Map.Strict                         as M
import           Data.Set                                 ( Set )
import           Data.Function                            ( (&) )

import           System.FilePath
import           Shelly                                  as Sh hiding ((</>))

import           Text.Mustache                           (substitute, automaticCompile)

import Paths_liquidhaskell

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
mirrorModules cli@CLI{..} = shelly $ silently $ do
  dataDir         <- liftIO getDataDir
  inputModules    <- S.fromList . map T.strip . T.words <$> readfile modulesList
  existingModules <- findExistingModules cli

  -- If the user decided to completely override existing files, simply return all the input modules.
  let notMirrored = if | unFlag overrideFiles -> inputModules
                       | otherwise            -> inputModules `S.difference` existingModules


  -- Use a template to automatically generate the module.
  let searchSpace = [dataDir </> "mirror-modules/templates"]
      templateName = "MirrorModule.mustache"

  compiled <- liftIO $ automaticCompile searchSpace templateName
  case compiled of
    Left err       -> errorExit (T.pack . show $ err)
    Right template -> do
      forM_ notMirrored $ \toMirror -> do
        let ctx = M.fromList [("packageName" :: String, mirroredPackage cli), ("moduleName", toMirror)]
        let newModule = substitute template ctx

        let pathToModule = moduleHierarchyRoot </> T.unpack (T.replace "." "/" toMirror) <> ".hs"
        parentFolder <- T.strip <$> run "dirname" [T.pack pathToModule]

        -- Create the parent folder, if necessary.
        mkdir_p (T.unpack parentFolder)

        -- Write the module.
        writefile pathToModule newModule

      echo $ "Mirrored " <> T.pack (show . length $ notMirrored) <> " modules."

main :: IO ()
main = mirrorModules =<< execParser opts
  where
    opts = info (parseCLI <**> helper)
      ( fullDesc
     <> progDesc "Create modules to be used in mirror packages."
     <> header "mirror-modules - Generate modules in mirror packages." )
