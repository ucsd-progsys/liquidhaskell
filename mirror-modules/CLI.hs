module CLI (
    CLI (..)
  , Flag(..)
  , parseCLI
  ) where


import Options.Applicative
import qualified Data.Text as T


-- Flags
data OverrideFiles

-- The @Flag@ datatype.

newtype Flag ix = Flag { unFlag :: Bool }

data CLI = CLI {
    overrideFiles       :: Flag OverrideFiles
  , modulesList         :: FilePath
  -- ^ A path to a list of modules to create.
  , mirrorPackageName   :: T.Text
  , moduleHierarchyRoot :: FilePath
  -- ^ A path to the root of the module hierarchy for the package we would like to target.
  }

parseCLI :: Parser CLI
parseCLI = CLI <$> parseOverrideFiles
               <*> parseModulesList
               <*> parsePackageName
               <*> parseModuleRoot

parseOverrideFiles :: Parser (Flag OverrideFiles)
parseOverrideFiles =
  Flag <$> switch (  long "unsafe-override-files"
                  <> help "Overrides an Haskell module if already present in the folder."
                  )

parseModulesList :: Parser FilePath
parseModulesList =
  strOption (  short 'l'
            <> long "modules-list"
            <> help "The path to a file containing a newline-separated list of modules to mirror."
            )

parsePackageName :: Parser T.Text
parsePackageName = T.pack <$>
  strOption (  short 'p'
            <> long "mirror-package-name"
            <> help "The name of the mirror package we are targeting. (example: liquid-foo)"
            )

parseModuleRoot :: Parser FilePath
parseModuleRoot =
  strOption (  short 'i'
            <> long "target"
            <> help "The path to the root of the module hierarchy for the target package. (example: liquid-foo/src)"
            )
