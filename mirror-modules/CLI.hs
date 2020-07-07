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
    overrideFiles :: Flag OverrideFiles
  , modulesList   :: FilePath
  -- ^ A path to a list of modules to create.
  , targetPackage :: FilePath
  -- ^ A path to a valid \"liquid-*\" package.
  }

parseCLI :: Parser CLI
parseCLI = CLI <$> parseOverrideFiles <*> parseModulesList <*> parseTargetPackage

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

parseTargetPackage :: Parser FilePath
parseTargetPackage =
  strOption (  short 't'
            <> long "target"
            <> help "The path to a target package we would like adding modules to."
            )
