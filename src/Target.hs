{-# LANGUAGE LambdaCase #-}
module Main where

import Language.Haskell.Interpreter
import System.Environment
import System.Exit
import System.IO
import Test.Target
import Text.Printf

main :: IO ()
main = do
  [src, binder] <- getArgs
  r <- runInterpreter $ do
    loadModules [src]
    mods <- getLoadedModules
    -- liftIO $ print mods
    setImportsQ $ map (\m -> (m,Nothing)) mods
                             ++ [("Test.Target", Nothing), ("Prelude", Nothing)]
    set [languageExtensions := [TemplateHaskell]]
    let expr = printf "$(targetResultTH '%s \"%s\")" binder src
    -- liftIO $ putStrLn expr
    interpret expr (as :: IO Result)
  case r of
    Left e -> hPrint stderr e >> exitWith (ExitFailure 2)
    Right x -> x >>= \case
      Errored e -> hPutStrLn stderr e >> exitWith (ExitFailure 2)
      Failed s  -> printf "Found counter-example: %s\n" s >> exitWith (ExitFailure 1)
      Passed n  -> printf "OK! Passed %d tests.\n" n >> exitSuccess
