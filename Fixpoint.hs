
import Language.Fixpoint.Interface (solveFile)
import System.Environment          (getArgs)

main = do files <- getArgs  
          case files of 
            [fq]     -> solveFile fq "out"
            [fq, fo] -> solveFile fq fo
            _        -> error "Usage: liquid-fixpoint input.fq output.out"

