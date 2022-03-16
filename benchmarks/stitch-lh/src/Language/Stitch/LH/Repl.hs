{-# LANGUAGE FlexibleInstances, UndecidableInstances, ViewPatterns,
             NondecreasingIndentation #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
-- XXX: Why do we need --exact-data-cons here?
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Repl
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Implements a REPL for stitch.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Repl ( main ) where

import Prelude hiding ( lex )

-- XXX: LH requires Map to be in scope ??
import Data.Map (Map)
import Language.Stitch.LH.Data.List (List)
import qualified Language.Stitch.LH.Data.List as List -- XXX: required by LH
import Language.Stitch.LH.Check
import Language.Stitch.LH.Eval
import Language.Stitch.LH.Lex
import Language.Stitch.LH.Parse
import Language.Stitch.LH.Step
import Language.Stitch.LH.Unchecked
import Language.Stitch.LH.Util
import Language.Stitch.LH.Statement
import Language.Stitch.LH.Monad
-- import Language.Stitch.LH.CSE
import Language.Stitch.LH.Type

import Text.PrettyPrint.ANSI.Leijen as Pretty hiding ( (<$>) )

import System.Console.Haskeline
import System.Directory

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as List

-- | The Stitch interpreter
main :: IO ()
main = runInputT defaultSettings $
       runStitch $ do
         helloWorld
         loop

{-@ lazy loop @-}
-- XXX: Omiting the type signature seems to synthetize
--      loop :: { v : Stitch () | false }
--      which disables validation everywere loop is used
--      and it also seems to synthetize { v : Stitch () | false }
--      for other functions used by loop that don't have
--      annotations either.
{-@ loop :: Stitch () @-}
loop :: Stitch ()
loop = do
  m_line <- prompt "λ> "
  case stripWhitespace <$> m_line of
    Nothing          -> quit
    Just (':' : cmd) -> runCommand cmd
    Just str         -> runStmts str
  loop

-- | Prints welcome message
helloWorld :: Stitch ()
helloWorld = do
  printLine $ text "Welcome to the Stitch interpreter, version" <+>
              text version <> char '.'
  printLine $ text "Type `:help` at the prompt for the list of commands."

-- | The current version of stitch
version :: String
version = "1.0"

-------------------------------------------
-- running statements

runStmts :: String -> Stitch ()
runStmts str = stitchE $
    lexM str >>= parseStmtsM >>= doStmts

-- | Run a sequence of statements, returning the new global variables
doStmts :: [Statement] -> StitchE Globals
doStmts []     = ask
doStmts (s:ss) = doStmt s $ doStmts ss

-- | Run a 'Statement' and then run another action with the global
-- variables built in the 'Statement'
doStmt :: Statement -> StitchE a -> StitchE a
doStmt (BareExp uexp) thing_inside = checkM uexp $ \e tye -> do
  printLine $ printValWithType (eval e) tye
  thing_inside
doStmt (NewGlobal g uexp) thing_inside =
  checkM uexp $ \e t -> do
    printLine $ text g <+> char '=' <+> printWithType (ScopedExp 0 e) t
    local (extendGlobals g (TypedExp e t)) thing_inside

-------------------------------------------
-- commands

-- | Interpret a command (missing the initial ':').
runCommand :: String -> Stitch ()
runCommand = dispatchCommand cmdTable

type CommandTable = [(String, String -> Stitch ())]

dispatchCommand :: CommandTable -> String -> Stitch ()
dispatchCommand table line_s
  = case List.filter ((cmd `List.isPrefixOf`) . fst) table of
      []            -> do printLine $ text "Unknown command:" <+> squotes (text cmd)
      [(_, action)] -> action arg
      many          -> do printLine $ text "Ambiguous command:" <+> squotes (text cmd)
                          printLine $ text "Possibilities:" $$
                                      indent 2 (vcat $ List.map (text . fst) many)
  where (cmd, arg) = List.break isSpace line_s

cmdTable :: CommandTable
cmdTable = [ ("quit",     quitCmd)
           , ("d-lex",    lexCmd)
           , ("d-parse",  parseCmd)
           , ("load",     loadCmd)
           , ("eval",     evalCmd)
           , ("step",     stepCmd)
           , ("type",     typeCmd)
           , ("all",      allCmd)
--           , ("cse",      cseCmd)
--           , ("cse-step", cseStepCmd)
           , ("help",     helpCmd)
           ]

quitCmd :: String -> Stitch ()
quitCmd _ = quit

class Reportable a where
  report :: a -> Stitch Globals

instance Reportable Doc where
  report x = printLine x >> get
instance Reportable () where
  report _ = get
instance Reportable Globals where
  report = return
instance {-# OVERLAPPABLE #-} Pretty a => Reportable a where
  report other = printLine (pretty other) >> get

stitchE :: Reportable a => StitchE a -> Stitch ()
stitchE thing_inside = do
  result <- runStitchE thing_inside
  new_globals <- case result of
    Left err -> printLine err >> get
    Right x  -> report x
  put new_globals

{-@ parseLex :: String -> StitchE ClosedUExp @-}
parseLex :: String -> StitchE UExp
parseLex = parseExpM <=< lexM

printWithType :: (Pretty exp, Pretty ty) => exp -> ty -> Doc
printWithType e tye
  = pretty e <+> colon <+> pretty tye

printValWithType :: Value -> Ty -> Doc
printValWithType val tye
  = pretty val <+> colon <+> pretty tye

{-@
// XXX: WellTypedExp Nil doesn't work here because it needs --ple,
// and --ple is not usable unless we get rid of the uses of the
// list type [a] in this module.
assume showSteps :: ty:Ty -> WellTypedExp Nil -> StitchE Int
ignore showSteps
@-}
showSteps :: Ty -> Exp -> StitchE Int
showSteps sty e0 = do
  printLine $ printWithType (ScopedExp 0 e0) sty
  let loopSteps num_steps e = case step e of
        Just e' -> do
          printLine $ text "-->" <+> printWithType (ScopedExp 0 e') sty
          loopSteps (num_steps + 1) e'
        Nothing -> return num_steps
  loopSteps 0 e0

lexCmd, parseCmd, evalCmd, typeCmd, loadCmd, allCmd, stepCmd -- , cseCmd, cseStepCmd
  , helpCmd
  :: String -> Stitch ()
lexCmd expr_s = stitchE $ lexM expr_s
parseCmd = stitchE . fmap (ScopedUExp 0) . parseLex

evalCmd expr_s = stitchE $ do
  uexp <- parseLex expr_s
  checkM uexp $ \e t ->
    return $ printValWithType (eval e) t

stepCmd expr_s = stitchE $ do
  uexp <- parseLex expr_s
  checkM uexp $ \e sty -> do
    _ <- showSteps sty e
    return ()

typeCmd expr_s = stitchE $ do
  uexp <- parseLex expr_s
  checkM uexp $ \e t ->
    return $ printWithType (ScopedExp 0 e) t

allCmd e = do
  printLine (text "Small step:")
  _ <- stepCmd e

  printLine Pretty.empty
  printLine (text "Big step:")
  evalCmd e

loadCmd (stripWhitespace -> file) = do
  file_exists <- liftIO $ doesFileExist file
  if not file_exists then file_not_found else do
  contents <- liftIO $ readFile file
  runStmts contents
  where
    file_not_found = do
      printLine (text "File not found:" <+> squotes (text file))
      cwd <- liftIO getCurrentDirectory
      printLine (parens (text "Current directory:" <+> text cwd))
{-
cseCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \_sty exp -> do
    printLine $ text "Before CSE:" <+> pretty exp
    printLine $ text "After CSE: " <+> pretty (cse exp)

cseStepCmd expr = stitchE $ do
  uexp <- parseLex expr
  check uexp $ \sty exp -> do
    printLine $ text "Before CSE:" <+> pretty exp
    n <- showSteps sty exp
    printLine $ text "Number of steps:" <+> pretty n

    printLine $ text "----------------------"

    let exp' = cse exp
    printLine $ text "After CSE: " <+> pretty exp'
    n' <- showSteps sty exp'
    printLine $ text "Number of steps:" <+> pretty n'

    return ()
-}
helpCmd _ = do
  printLine $ text "Available commands:"
  printLine $ text " :quit             Quits the interpreter"
  printLine $ text " :load <filename>  Loads a file with ;-separated Stitch statements"
  printLine $ text " :eval <expr>      Evaluates an expression with big-step semantics"
  printLine $ text " :step <expr>      Small-steps an expression until it becomes a value"
  printLine $ text " :type <expr>      Type-check an expression and report the type"
  printLine $ text " :all <expr>       Combination of :eval and :step"
--  printLine $ text " :cse <expr>       Performs common-subexpression elimination (CSE)"
--  printLine $ text " :cse-step <expr>  Steps an expression both before and after CSE"
  printLine $ text " :help             Shows this help text"
  printLine $ text "You may also type an expression to evaluate it, or assign to a global"
  printLine $ text "variable with `<var> = <expr>`"

checkM :: UExp -> (Exp -> Ty -> StitchE a) -> StitchE a
checkM uexp f = do
  globals <- ask
  either (issueError . pretty) id $ check globals uexp $ \e t -> Right (f e t)
