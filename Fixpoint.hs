
import Language.Fixpoint.Interface (solveFile)
import System.Environment          (getArgs)
import System.Console.GetOpt
import Language.Fixpoint.Types     (SMTSolver(..))

main = do (smt, files) <- parseOpts =<< getArgs  
          case files of 
            [fq]     -> solveFile smt fq "out"
            [fq, fo] -> solveFile smt fq fo
            _        -> error "Usage: fixpoint input.fq output.out"
 
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
    
options :: [OptDescr SMTSolver]
options = [ Option ['s'] ["smtsolver"] (ReqArg solver "SMTSOLVER")  "name of SMT solver [z3, mathsat, cvc4,...]"
          ]

parseOpts :: [String] -> IO (Maybe SMTSolver, [String])
parseOpts argv = 
   case getOpt Permute options argv of
     (o:_, n, []  ) -> return (Just o , n)
     ([] , n, []  ) -> return (Nothing, n)
     (_  ,_ , errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Usage: fixpoint [OPTION...] file.fq output.out" 



solver "z3"      = Z3
solver "cvc4"    = CVC4
solver "mathsat" = MathSat
solver other     = error $ "ERROR: cannot use solver = " ++ other


