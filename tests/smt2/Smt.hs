-- just fire up ghci, :load Smt.hs and run `go file.smt2`

module Smt where

import qualified Data.Text.Lazy.IO as T

import Language.Fixpoint.Config (SMTSolver (..))
import Language.Fixpoint.Parse
import Language.Fixpoint.SmtLib2
import System.Environment

main    = do f:_ <- getArgs
             _   <- go f
             return ()

go file = do cmds <- fmap rr $ readFile file
             me   <- makeContext Z3
             mapM_ (T.putStrLn . smt2) cmds
             zs   <- mapM (command me) cmds
             return zs
