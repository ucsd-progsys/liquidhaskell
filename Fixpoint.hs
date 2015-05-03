import Language.Fixpoint.Interface     (solveFQ)
import Language.Fixpoint.Config        (getOpts)
import System.Exit
import System.Console.CmdArgs.Verbosity (whenLoud)

main :: IO ExitCode
main = do cfg <- getOpts
          whenLoud $ putStrLn $ "Options: " ++ show cfg
          e <- solveFQ cfg
          putStrLn $ "EXIT: " ++ show e
          exitWith e
