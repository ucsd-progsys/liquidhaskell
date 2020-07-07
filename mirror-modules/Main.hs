
module Main where

import CLI
import Options.Applicative


main :: IO ()
main = mirrorModules =<< execParser opts
  where
    opts = info (parseCLI <**> helper)
      ( fullDesc
     <> progDesc "Create modules to be used in mirror packages."
     <> header "mirror-modules - Generate modules in mirror packages." )


mirrorModules :: CLI -> IO ()
mirrorModules _ = putStrLn "todo"
