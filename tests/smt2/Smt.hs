import Language.Fixpoint.Config (SMTSolver (..))
import Language.Fixpoint.Parse
import Language.Fixpoint.SmtLib2
import System.Environment

main    = do f:_ <- getArgs
             go f

go file = do cmds <- fmap rr $ readFile file
             me   <- makeContext Z3
             putStrLn $ show $ map smt2 cmds
             zs   <- mapM (command me) cmds
             return zs
