{-# LANGUAGE TupleSections #-}

module Main where

import Language.Haskell.Liquid.Liquid (liquidConstraints)

import Language.Haskell.Liquid.Types (GhcInfo(..), Cinfo) 
import Language.Haskell.Liquid.Constraint.Types (CGInfo(..)) -- , FixWfC, SubC(..), CGEnv(..))
import Language.Haskell.Liquid.UX.Config (Config(..))
import Language.Haskell.Liquid.UX.CmdLine (getOpts)
import Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo, fixConfig)

import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as F
import           Language.Fixpoint.Solver       (simplifyFInfo)
import           Language.Fixpoint.Solver.Solve (solve)
import qualified Language.Fixpoint.Solver.GradualSolution as GS
import           Language.Fixpoint.Misc         (mapSnd)
import           Language.Fixpoint.Graph.Partition (partition')

import System.Exit                    (exitWith, exitSuccess, exitFailure)
import System.Environment             (getArgs)
import System.Console.CmdArgs.Verbosity
import Control.Monad (when) 

import qualified Data.List as L 

import Gradual.Concretize 
import Gradual.Types
import Gradual.Misc (mapSndM, mapMWithLog)
import Gradual.Uniquify
import Gradual.Refinements
import Gradual.PrettyPrinting
import qualified Gradual.GUI as GUI
import qualified Gradual.Trivial as T 

main :: IO a
main = do 
  cfg <- getArgs >>= getOpts
  css <- quietly $ liquidConstraints (cfg{gradual=True})
  case css of 
    Left cgis -> mapM (runGradual (cfg{gradual=True})) cgis >> exitSuccess 
    Right e   -> exitWith e 


runGradual :: Config -> CGInfo -> IO [(GSub F.GWInfo,F.Result (Integer, Cinfo))]
runGradual cfg cgi = do
  let fname    = target (ghcI cgi)
  let fcfg     = fixConfig fname cfg
  finfo       <- quietly $ cgInfoFInfo (ghcI cgi) cgi
  sinfo <- (uniquify . T.simplify) <$> (quietly $ simplifyFInfo fcfg finfo)
  let (gsis, sis) = L.partition F.isGradual $ partition' Nothing (snd sinfo)
  let gcfg     = (makeGConfig cfg) {pNumber = length gsis}
  sol <- mconcat <$> (quietly $ mapM (solve fcfg) sis)
  let gcfgs = setPId gcfg <$> [1..(length gsis)]
  when (not $ F.isSafe sol) $ do 
    putStrLn "The static part cannot be satisfied: UNSAFE"
    exitFailure
  whenLoud $ putStrLn ("\nNumber of Gradual Partitions : " ++ show (length gsis) ++"\n")
  solss <- mapMWithLog "Running Partition" (uncurry $ solveSInfo fcfg) (zip gcfgs gsis)
  GUI.render gcfg (fst sinfo) solss
  exitSuccess



solveSInfo :: F.Config  -> GConfig -> F.SInfo Cinfo -> IO [GSub F.GWInfo]
solveSInfo fcfg gcfg sinfo = do 
  gmap     <- makeGMap gcfg fcfg sinfo $ GS.init fcfg sinfo 
  let allgs = concretize gmap sinfo
  putStrLn ("Total number of concretizations: " ++ show (length $ map snd allgs))
  res   <- quietly $ mapM (mapSndM (solve fcfg)) allgs
  case filter (F.isSafe . snd) res of 
    (x:xs) -> do putStrLn ( "["++ show (1 + length xs) ++ "/" ++ (show $ length res) ++ "] Solutions Found!" ++ if length xs > 0 then " e.g.," else "") 
                 putStrLn (pretty $ (map (mapSnd snd) $ fromGSub $ fst x))
                 return (fst <$> (x:xs))
    _     -> do putStrLn ("[0/" ++ (show $ length res) ++ "] Solutions. UNSAFE!\n")  
                whenLoud $ putStrLn ("UNSAFE PARTITION: " ++ show sinfo)                           
                return [mempty] 

quietly :: IO a -> IO a 
quietly act = do 
  vb <- getVerbosity 
  setVerbosity Quiet
  r  <- act 
  setVerbosity vb 
  return r 
