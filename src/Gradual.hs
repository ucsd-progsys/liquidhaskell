{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns  #-}

module Main where

import Language.Haskell.Liquid.Liquid (liquidConstraints)

import Language.Haskell.Liquid.Types (GhcInfo(..), Cinfo, HasConfig(..)) 
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

import Gradual.Log 
import Gradual.Concretize 
import Gradual.Types
import Gradual.Misc (mapMWithLog)
import Gradual.Uniquify
import Gradual.Refinements
import Gradual.PrettyPrinting
import qualified Gradual.GUI as GUI
import qualified Gradual.Trivial as T 
import Gradual.Match 

main :: IO a
main = do 
  cfg <- getArgs >>= getOpts
  css <- quietly $ liquidConstraints (cfg{gradual=True, eliminate = F.None})
  case css of 
    Left cgis -> mapM runGradual cgis >> exitSuccess 
    Right e   -> exitWith e 


runGradual :: CGInfo -> IO [(GSub F.GWInfo,F.Result (Integer, Cinfo))]
runGradual cgi = do
  let cfg      = (getConfig cgi){gradual=True}
  logDepth (gdepth cfg)
  let fname    = target (ghcI cgi)
  let fcfg     = fixConfig fname cfg
  finfo       <- quietly $ cgInfoFInfo (ghcI cgi) cgi
  let tx       = if (gsimplify cfg) then T.simplify else id
  sinfo <- (uniquify . tx) <$> (quietly $ simplifyFInfo fcfg finfo)
  logSpans (fst sinfo)
  parts <- logParts $ partition' Nothing (snd sinfo)
  let (gsis, sis) = L.partition F.isGradual parts
  logGParts gsis
  let gcfg     = (makeGConfig cfg) {pNumber = length gsis}
  sol <- mconcat <$> (quietly $ mapM (solve fcfg) sis)
  let gcfgs = setPId gcfg <$> [1..(length gsis)]
  when (not $ F.isSafe sol) $ do 
    putStrLn "The static part cannot be satisfied: UNSAFE"
    exitFailure
  whenLoud $ putStrLn ("\nNumber of Gradual Partitions : " ++ show (length gsis) ++"\n")
  solss <- mapMWithLog "Running Partition" (uncurry $ solveSInfo fcfg) (zip gcfgs gsis)
  GUI.render gcfg (fst sinfo) solss
  let ssols = matchSolutions (fst sinfo) solss 
  logMatches ssols 
  printLog
  exitSuccess



solveSInfo :: F.Config  -> GConfig -> F.SInfo Cinfo -> IO [GSub F.GWInfo]
solveSInfo !fcfg !gcfg !sinfo = do 
  gmap     <- makeGMap gcfg fcfg sinfo $ GS.init fcfg sinfo 
  allgs    <- logConcr $ concretize gmap sinfo
  putStrLn ("Total number of concretizations: " ++ show (length $ map snd allgs))
  res   <- solveWhile fcfg 1001 (take 1000 allgs)
  -- res   <- quietly $ mapM (solve' fcfg) (zip allgs [1..])
  case res of 
    (x:xs) -> do putStrLn ( "["++ show (1 + length xs) ++ "/" ++ (show $ length allgs) ++ "] Solutions Found!" ++ if length xs > 0 then " e.g.," else "") 
                 putStrLn (pretty $ (map (mapSnd snd) $ fromGSub $ fst x))
                 logSol (x:xs)
                 return (fst <$> (x:xs))
    _     -> do putStrLn ("[0/" ++ (show $ length allgs) ++ "] Solutions. UNSAFE!\n")  
                whenLoud $ putStrLn ("UNSAFE PARTITION: " ++ show sinfo)  
                logSol ([])
                return [mempty] 

solveWhile :: F.Config -> Int -> [(a, F.SInfo Cinfo)] -> IO [(a, F.Result (Integer, Cinfo))]
solveWhile cfg m xs = go [] xs
  where
    go !acc [] = return acc 
    go !acc ((x, y):xs) = do 
      r <- solve cfg y 
      if F.isSafe r then
         if length acc == m -1 
            then return ((x,r):acc)
            else go ((x,r):acc) xs 
      else go acc xs
  


quietly :: IO a -> IO a 
quietly act = do 
  vb <- getVerbosity 
  setVerbosity Quiet
  r  <- act 
  setVerbosity vb 
  return r 
