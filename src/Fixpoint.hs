import Language.Fixpoint.Solver        (solveFQ)
import Language.Fixpoint.Types.Config  (getOpts)
import System.Exit
import Language.Fixpoint.Misc    (writeLoud)

main = do
  cfg <- getOpts
  writeLoud $  "Options: " ++ show cfg
  e <- solveFQ cfg
  exitWith e

