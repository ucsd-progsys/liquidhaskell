
import Language.Fixpoint.Interface     (solveFile)
import System.Environment              (getArgs)
-- import System.Console.GetOpt
import Language.Fixpoint.Config hiding (config)
import Data.Maybe                      (fromMaybe, listToMaybe)
import System.Console.CmdArgs                  
import System.Console.CmdArgs.Verbosity (whenLoud)



main = do cfg <- getOpts 
          whenLoud $ putStrLn $ "Options: " ++ show cfg
          solveFile cfg

config = Config { 
    inFile   = def   &= typ "TARGET"       &= args    &= typFile 
  , outFile  = "out" &= help "Output file"  
  , solver   = def   &= help "Name of SMT Solver" 
  , genSorts = def   &= help "Generalize qualifier sorts"
}  &= verbosity
   &= program "fixpoint" 
   &= help    "Predicate Abstraction Based Horn-Clause Solver" 
   &= summary "fixpoint © Copyright 2009-13 Regents of the University of California." 
   &= details [ "Predicate Abstraction Based Horn-Clause Solver"
              , ""
              , "To check a file foo.fq type:"
              , "  fixpoint foo.fq"
              ]

getOpts :: IO Config 
getOpts = do md <- cmdArgs config 
             putStrLn $ banner md
             return md

banner args =  "Liquid-Fixpoint © Copyright 2009-13 Regents of the University of California.\n" 
            ++ "All Rights Reserved.\n"
