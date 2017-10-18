module Main where

import Language.Haskell.Liquid.Liquid (liquidConstraints)

import Language.Haskell.Liquid.Types (GhcInfo(..), Cinfo) 
import Language.Haskell.Liquid.Constraint.Types (CGInfo(..)) -- , FixWfC, SubC(..), CGEnv(..))
import Language.Haskell.Liquid.UX.Config (Config(..))
import Language.Haskell.Liquid.UX.CmdLine (getOpts)
import Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo, fixConfig)

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Solver       (simplifyFInfo)
import           Language.Fixpoint.Solver.Solve (solve)
import qualified Language.Fixpoint.Solver.GradualSolution as GS


import System.Exit                    (exitWith, exitSuccess, exitFailure)
import System.Environment             (getArgs)


import Gradual.Concretize 
import Gradual.Types
import Gradual.Uniquify
import Gradual.Refinements

main :: IO a
main = do 
  cfg <- getArgs >>= getOpts
  css <- liquidConstraints (cfg{gradual=True})
  case css of 
    Left cgis -> mapM (runGradual cfg) cgis >> exitSuccess 
    Right e   -> exitWith e 


runGradual :: Config -> CGInfo -> IO [F.Result (Integer, Cinfo)]
runGradual cfg cgi = do
  let fname = target (ghcI cgi)
  let fcfg  = fixConfig fname cfg
  finfo    <- cgInfoFInfo (ghcI cgi) cgi
  sinfo    <- uniquify <$> simplifyFInfo fcfg finfo
  gmap     <- makeGMap fcfg sinfo $ GS.init sinfo 
  putStrLn ("\nGMAP = \n" ++ show gmap
      ++ concat [show (length $ snd x) ++ "\n" | (_,x) <- fromGMap gmap ]
      ++ "\nALL COMB = " ++ show (product [(length $ snd x) | (_,x) <- fromGMap gmap ])
   )
  -- putStrLn ("\nSinfo = \n" ++ show sinfo)
  let allgs = concretize gmap sinfo
  putStrLn ("\nAll CS = \n" ++ show (length allgs))
  res   <- mapM (solve fcfg) allgs
  case filter F.isSafe res of 
    (_:xs) -> putStrLn (show (1 + length xs) ++ "/" ++ (show $ length res) ++ " Solutions Found!") 
             >> exitSuccess
    _     -> putStrLn ("0/" ++ (show $ length res) ++ " UNSAFE!")                            
             >> exitFailure
