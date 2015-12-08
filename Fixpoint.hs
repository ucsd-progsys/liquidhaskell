import Language.Fixpoint.Interface     (solveFQ)
import Language.Fixpoint.Config        (getOpts)
import System.Exit
import Language.Fixpoint.Misc (writeLoud)

main = do
  cfg <- getOpts
  writeLoud $  "Options: " ++ show cfg
  e <- solveFQ cfg
  exitWith e

