module CLI (
    CLI (..)
  , Flag(..)
  , parseCLI
  ) where


import Options.Applicative


-- Flags
data OverrideFiles

-- The @Flag@ datatype.

newtype Flag ix = Flag { unFlag :: Bool }

data CLI = CLI {
    overrideFiles       :: Flag OverrideFiles
  , modulesList         :: FilePath
  -- ^ A path to a list of modules to create.
  , moduleHierarchyRoot :: FilePath
  -- ^ A path to the root of the module hierarchy for the package we would like to target.
  }

parseCLI :: Parser CLI
parseCLI = CLI <$> parseOverrideFiles <*> parseModulesList <*> parseModuleRoot

parseOverrideFiles :: Parser (Flag OverrideFiles)
parseOverrideFiles =
  Flag <$> switch (  long "unsafe-override-files"
                  <> help "Overrides an Haskell module if already present in the folder."
                  )

parseModulesList :: Parser FilePath
parseModulesList =
  strOption (  short 'i'
            <> long "modules-list"
            <> help "The path to a file containing a newline-separated list of modules to mirror."
            )

parseModuleRoot :: Parser FilePath
parseModuleRoot =
  strOption (  short 't'
            <> long "target"
            <> help "The path to the root of the module hierarchy for the target package. (example: liquid-foo/src)"
            )
