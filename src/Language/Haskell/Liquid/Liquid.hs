{-# LANGUAGE TupleSections  #-}

{-@ LIQUID "--diff"     @-}

module Language.Haskell.Liquid.Liquid (
   -- * Executable command
    liquid

   -- * Single query
  , runLiquid

   -- * Ghci State
  , MbEnv
  ) where

import           Data.Maybe
import           System.Exit
import           Control.DeepSeq
import           Text.PrettyPrint.HughesPJ
import           CoreSyn
import           Var
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Console.CmdArgs.Default
import           GHC (HscEnv)

import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Solver
import           Language.Fixpoint.Types (sinfo, Result (..)) -- , FixResult (..))
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.UX.Annotate (mkOutput)


type MbEnv = Maybe HscEnv

------------------------------------------------------------------------------
liquid :: [String] -> IO b
------------------------------------------------------------------------------
liquid args = getOpts args >>= runLiquid Nothing >>= exitWith . fst

------------------------------------------------------------------------------
-- | This fellow does the real work
------------------------------------------------------------------------------
runLiquid :: MbEnv -> Config -> IO (ExitCode, MbEnv)
------------------------------------------------------------------------------
runLiquid mE cfg = do
  (d, mE') <- checkMany cfg mempty mE (files cfg)
  return      (ec d, mE')
  where
    ec     = resultExit . o_result


-- filesTimes3 cfg = case files cfg of
--                    [f] -> [f, f, f]
--                     fs  -> fs


------------------------------------------------------------------------------
checkMany :: Config -> Output Doc -> MbEnv -> [FilePath] -> IO (Output Doc, MbEnv)
------------------------------------------------------------------------------
checkMany cfg d mE (f:fs) = do
  (d', mE') <- checkOne mE cfg f
  checkMany cfg (d `mappend` d') mE' fs

checkMany _   d mE [] =
  return (d, mE)

------------------------------------------------------------------------------
checkOne :: MbEnv -> Config -> FilePath -> IO (Output Doc, Maybe HscEnv)
------------------------------------------------------------------------------
checkOne mE cfg t = do
  z <- getGhcInfo mE cfg t
  case z of
    Left e -> do
      d <- exitWithResult cfg t $ mempty { o_result = e }
      return (d, Nothing)
    Right (gInfo, hEnv) -> do
      d <- liquidOne t gInfo
      return (d, Just hEnv)


------------------------------------------------------------------------------
liquidOne :: FilePath -> GhcInfo -> IO (Output Doc)
------------------------------------------------------------------------------
liquidOne tgt info = do
  donePhase Loud "Extracted Core using GHC"
  let cfg   = config $ spec info
  whenLoud  $ do putStrLn "**** Config **************************************************"
                 print cfg
  whenLoud  $ do putStrLn $ showpp info
                 putStrLn "*************** Original CoreBinds ***************************"
                 putStrLn $ render $ pprintCBs (cbs info)
  let cbs' = transformScope (cbs info)
  whenLoud  $ do donePhase Loud "transformRecExpr"
                 putStrLn "*************** Transform Rec Expr CoreBinds *****************"
                 putStrLn $ render $ pprintCBs cbs'
                 putStrLn "*************** Slicing Out Unchanged CoreBinds *****************"
  dc <- prune cfg cbs' tgt info
  let cbs'' = maybe cbs' DC.newBinds dc
  let info' = maybe info (\z -> info {spec = DC.newSpec z}) dc
  let cgi   = {-# SCC "generateConstraints" #-} generateConstraints $! info' {cbs = cbs''}
  cgi `deepseq` donePhase Loud "generateConstraints"
  out      <- solveCs cfg tgt cgi info' dc
  donePhase Loud "solve"
  let out'  = mconcat [maybe mempty DC.oldOutput dc, out]
  DC.saveResult tgt out'
  exitWithResult cfg tgt out'

checkedNames ::  Maybe DC.DiffCheck -> Maybe [String]
checkedNames dc          = concatMap names . DC.newBinds <$> dc
   where
     names (NonRec v _ ) = [render . text $ shvar v]
     names (Rec xs)      = map (shvar . fst) xs
     shvar               = showpp . varName

prune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Maybe DC.DiffCheck)
prune cfg cbinds tgt info
  | not (null vs) = return . Just $ DC.DC (DC.thin cbinds vs) mempty sp
  | diffcheck cfg = DC.slice tgt cbinds sp
  | otherwise     = return Nothing
  where
    vs            = tgtVars sp
    sp            = spec info

solveCs :: Config -> FilePath -> CGInfo -> GhcInfo -> Maybe DC.DiffCheck -> IO (Output Doc)
solveCs cfg tgt cgi info dc
  = do finfo        <- cgInfoFInfo info cgi tgt
       Result r sol <- solve fx finfo
       let names = checkedNames dc
       let warns = logErrors cgi
       let annm  = annotMap cgi
       let res   = ferr sol r
       let out0  = mkOutput cfg res sol annm
       return    $ out0 { o_vars = names } { o_errors  = warns} { o_result = res }
    where
       fx        = def { FC.solver      = fromJust (smtsolver cfg)
                       , FC.real        = real        cfg
                       , FC.newcheck    = newcheck    cfg
                    -- , FC.extSolver   = extSolver   cfg
                       , FC.eliminate   = eliminate   cfg
                       , FC.save        = saveQuery cfg
                       , FC.srcFile     = tgt
                       , FC.cores       = cores       cfg
                       , FC.minPartSize = minPartSize cfg
                       , FC.maxPartSize = maxPartSize cfg
                       -- , FC.stats   = True
                       }
       ferr s r  = tidyError s <$> result r


-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
