{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--diff"     @-}

module Language.Haskell.Liquid.Liquid (
   -- * Executable command
    liquid

   -- * Single query
  , runLiquid

   -- * Ghci State
  , MbEnv
  ) where

import           Prelude hiding (error)
import           Data.Maybe
import           System.Exit
-- import           Control.DeepSeq
import           Text.PrettyPrint.HughesPJ
import           CoreSyn
import           Var
import           HscTypes                         (SourceError)
import           System.Console.CmdArgs.Verbosity (whenLoud, whenNormal)
import           System.Console.CmdArgs.Default
import           GHC (HscEnv)

import qualified Control.Exception as Ex
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Tidy
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
  z <- actOrDie (checkOne' mE cfg t)
  case z of
    Left e -> do
      d <- exitWithResult cfg t $ mempty { o_result = e }
      return (d, Nothing)
    Right r ->
      return r


checkOne' :: MbEnv -> Config -> FilePath -> IO (Output Doc, Maybe HscEnv)
checkOne' mE cfg t = do
  (gInfo, hEnv) <- getGhcInfo mE cfg t
  d <- liquidOne t gInfo
  return (d, Just hEnv)


actOrDie :: IO a -> IO (Either ErrorResult a)
actOrDie act =
    (Right <$> act)
      `Ex.catch` (\(e :: SourceError) -> handle e)
      `Ex.catch` (\(e :: Error)       -> handle e)
      `Ex.catch` (\(e :: UserError)   -> handle e)
      `Ex.catch` (\(e :: [Error])     -> handle e)

handle :: (Result a) => a -> IO (Either ErrorResult b)
handle = return . Left . result

------------------------------------------------------------------------------
liquidOne :: FilePath -> GhcInfo -> IO (Output Doc)
------------------------------------------------------------------------------
liquidOne tgt info = do
  whenNormal $ donePhase Loud "Extracted Core using GHC"
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
  -- cgi `deepseq` whenLoud (donePhase Loud "generateConstraints")
  whenLoud  $ dumpCs cgi
  out      <- solveCs cfg tgt cgi info' dc
  whenNormal $ donePhase Loud "solve"
  let out'  = mconcat [maybe mempty DC.oldOutput dc, out]
  DC.saveResult tgt out'
  exitWithResult cfg tgt out'

dumpCs :: CGInfo -> IO ()
dumpCs cgi = do
  putStrLn "***************************** SubCs *******************************"
  putStrLn $ render $ pprintMany (hsCs cgi)
  putStrLn "***************************** FixCs *******************************"
  putStrLn $ render $ pprintMany (fixCs cgi)
  putStrLn "***************************** WfCs ********************************"
  putStrLn $ render $ pprintMany (hsWfs cgi)

pprintMany :: (PPrint a) => [a] -> Doc
pprintMany xs = vcat [ F.pprint x $+$ text " " | x <- xs ]

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
       F.Result r sol <- solve fx finfo
       let names = checkedNames dc
       let warns = logErrors cgi
       let annm  = annotMap cgi
       let res   = ferr sol r
       let out0  = mkOutput cfg res sol annm
       return    $ out0 { o_vars    = names             }
                        { o_errors  = e2u sol <$> warns }
                        { o_result  = res               }
    where
       fx        = def { FC.solver      = fromJust (smtsolver cfg)
                       , FC.linear      = linear      cfg
                       , FC.newcheck    = newcheck    cfg
                       -- , FC.extSolver   = extSolver   cfg
                       , FC.eliminate   = eliminate   cfg
                       , FC.save        = saveQuery cfg
                       , FC.srcFile     = tgt
                       , FC.cores       = cores       cfg
                       , FC.minPartSize = minPartSize cfg
                       , FC.maxPartSize = maxPartSize cfg
                       , FC.elimStats   = elimStats   cfg
                       -- , FC.stats   = True
                       }
       ferr s  = fmap (cinfoUserError s . snd)


cinfoUserError   :: F.FixSolution -> (a, Cinfo) -> UserError
cinfoUserError s =  e2u s . cinfoError . snd

e2u :: F.FixSolution -> Error -> UserError
e2u s = fmap F.pprint . tidyError s

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
