{-# LANGUAGE NamedFieldPuns      #-}
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

   -- * Liquid Constraint Generation 
  , liquidConstraints

  -- * Internal (provisional)
  , liquidOne
  ) where

import           Prelude hiding (error)
import           Data.Bifunctor
import qualified Data.HashSet as S 
import           System.Exit
import           Text.PrettyPrint.HughesPJ
import           Var                              (Var)
import           CoreSyn
import           HscTypes                         (SourceError)
import           GHC (HscEnv)
import           System.Console.CmdArgs.Verbosity (whenLoud, whenNormal)
import           Control.Monad (when)
import qualified Control.Exception as Ex
-- import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import           Language.Haskell.Liquid.Misc
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType (applySolution)
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.GHC.Misc (showCBs, ignoreCoreBinds) -- howPpr)
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
-- import           Language.Haskell.Liquid.Model
-- import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.UX.Annotate (mkOutput)
import qualified Language.Haskell.Liquid.Termination.Structural as ST

import GhcPlugins (showSDocUnsafe, ppr)
import qualified Debug.Trace as Debug

type MbEnv = Maybe HscEnv



--------------------------------------------------------------------------------
liquid :: [String] -> IO b
--------------------------------------------------------------------------------
liquid args = do 
  cfg     <- getOpts args 
  (ec, _) <- runLiquid Nothing cfg
  exitWith ec

--------------------------------------------------------------------------------
liquidConstraints :: Config -> IO (Either [CGInfo] ExitCode) 
--------------------------------------------------------------------------------
liquidConstraints cfg = do 
  z <- actOrDie $ second Just <$> getGhcInfos Nothing cfg (files cfg)
  case z of
    Left e -> do
      exitWithResult cfg (files cfg) $ mempty { o_result = e }
      return $ Right $ resultExit e 
    Right (gs, _) -> 
      return $ Left $ map generateConstraints gs

--------------------------------------------------------------------------------
runLiquid :: MbEnv -> Config -> IO (ExitCode, MbEnv)
--------------------------------------------------------------------------------
runLiquid mE cfg  = do 
  reals <- realTargets mE cfg (files cfg)
  whenNormal $ putStrLn $ showpp (text "Targets:" <+> vcat (text <$> reals))
  checkTargets cfg mE reals

checkTargets :: Config -> MbEnv -> [FilePath] -> IO (ExitCode, MbEnv)
checkTargets cfg  = go 
  where
    go env []     = return (ExitSuccess, env)
    go env (f:fs) = do whenLoud $ colorPhaseLn Loud ("[Checking: " ++ f ++ "]") ""
                       (ec, env') <- runLiquidTargets env cfg [f] 
                       case ec of 
                         ExitSuccess -> go env' fs
                         _           -> return (ec, env')


--------------------------------------------------------------------------------
-- | @runLiquid@ checks a *target-list* of files, ASSUMING that we have 
--   already  run LH on ALL the (transitive) home imports -- i.e. other 
--   imports files for which we have source -- in order to build the .bspec 
--   files for those specs.
--------------------------------------------------------------------------------
runLiquidTargets :: MbEnv -> Config -> [FilePath] -> IO (ExitCode, MbEnv)
--------------------------------------------------------------------------------
runLiquidTargets mE cfg targetFiles = do
  z <- actOrDie $ second Just <$> getGhcInfos mE cfg targetFiles
  case z of
    Left e -> do
      exitWithResult cfg targetFiles $ mempty { o_result = e }
      return (resultExit e, mE)
    Right (gs, mE') -> do
      d <- checkMany cfg mempty gs
      return (ec d, mE')
  where
    ec = resultExit . o_result

--------------------------------------------------------------------------------
checkMany :: Config -> Output Doc -> [GhcInfo] -> IO (Output Doc)
--------------------------------------------------------------------------------
checkMany cfg d (g:gs) = do
  d' <- checkOne cfg g
  checkMany cfg (d `mappend` d') gs

checkMany _   d [] =
  return d

--------------------------------------------------------------------------------
checkOne :: Config -> GhcInfo -> IO (Output Doc)
--------------------------------------------------------------------------------
checkOne cfg g = do
  z <- actOrDie $ liquidOne g
  case z of
    Left  e -> exitWithResult cfg [giTarget (giSrc g)] $ mempty { o_result = e }
    Right r -> return r


actOrDie :: IO a -> IO (Either ErrorResult a)
actOrDie act =
    (Right <$> act)
      `Ex.catch` (\(e :: SourceError) -> handle e)
      `Ex.catch` (\(e :: Error)       -> handle e)
      `Ex.catch` (\(e :: UserError)   -> handle e)
      `Ex.catch` (\(e :: [Error])     -> handle e)

handle :: (Result a) => a -> IO (Either ErrorResult b)
handle = return . Left . result

--------------------------------------------------------------------------------
liquidOne :: GhcInfo -> IO (Output Doc)
--------------------------------------------------------------------------------
liquidOne info
  | compileSpec cfg = do 
    donePhase Loud "Only compiling specifications [skipping verification]"
    exitWithResult cfg [tgt] (mempty { o_result = F.Safe })
  | otherwise = do
    whenNormal $ donePhase Loud "Extracted Core using GHC"
    -- whenLoud  $ do putStrLn $ showpp info
                 -- putStrLn "*************** Original CoreBinds ***************************"
                 -- putStrLn $ render $ pprintCBs (cbs info)
    whenNormal $ donePhase Loud "Transformed Core"
    whenLoud  $ do donePhase Loud "transformRecExpr"
                   putStrLn "*************** Transform Rec Expr CoreBinds *****************"
                   putStrLn $ showCBs (untidyCore cfg) cbs'
                   -- putStrLn $ render $ pprintCBs cbs'
                   -- putStrLn $ showPpr cbs'
    edcs <- newPrune      cfg cbs' tgt info
    out' <- liquidQueries cfg      tgt info edcs
    DC.saveResult       tgt  out'
    exitWithResult cfg [tgt] out'
  where 
    cfg  = getConfig info
    tgt  = giTarget (giSrc info)
    cbs' = Debug.traceShow ("coreBinds ==> " ++ showSDocUnsafe (ppr $ giCbs (giSrc info))) (giCbs (giSrc info) )

newPrune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Either [CoreBind] [DC.DiffCheck])
newPrune cfg cbs tgt info
  | not (null vs) = return . Right $ [DC.thin cbs sp vs]
  | timeBinds cfg = return . Right $ [DC.thin cbs sp [v] | v <- expVars]
  | diffcheck cfg = maybeEither cbs <$> DC.slice tgt cbs sp
  | otherwise     = return $ Left (ignoreCoreBinds ignores cbs)
  where
    ignores       = gsIgnoreVars (gsVars sp)
    vs            = gsTgtVars    (gsVars sp)
    sp            = giSpec       info
    expVars       = exportedVars (giSrc info)

exportedVars :: GhcSrc -> [Var]
exportedVars src = filter (isExportedVar src) (giDefVars src)

maybeEither :: a -> Maybe b -> Either a [b]
maybeEither d Nothing  = Left d
maybeEither _ (Just x) = Right [x]

liquidQueries :: Config -> FilePath -> GhcInfo -> Either [CoreBind] [DC.DiffCheck] -> IO (Output Doc)
liquidQueries cfg tgt info (Left cbs')
  = liquidQuery cfg tgt info (Left cbs')
liquidQueries cfg tgt info (Right dcs)
  = mconcat <$> mapM (liquidQuery cfg tgt info . Right) dcs

liquidQuery   :: Config -> FilePath -> GhcInfo -> Either [CoreBind] DC.DiffCheck -> IO (Output Doc)
liquidQuery cfg tgt info edc = do
  let names   = either (const Nothing) (Just . map show . DC.checkedVars)   edc
  let oldOut  = either (const mempty)  DC.oldOutput                         edc
  let info1   = either (const info)    (\z -> info {giSpec = DC.newSpec z}) edc
  let cbs''   = either id              DC.newBinds                          edc
  let info2   = info1 { giSrc = (giSrc info1) {giCbs = cbs''}}
  let info3   = updGhcInfoTermVars info2 
  let cgi     = {-# SCC "generateConstraints" #-} generateConstraints $! info3 
  when False (dumpCs cgi)
  -- whenLoud $ mapM_ putStrLn [ "****************** CGInfo ********************"
                            -- , render (pprint cgi)                            ]
  out        <- timedAction names $ solveCs cfg tgt cgi info3 names
  return      $ mconcat [oldOut, out]

updGhcInfoTermVars    :: GhcInfo -> GhcInfo 
updGhcInfoTermVars i  = updInfo i  (ST.terminationVars i) 
  where 
    updInfo   info vs = info { giSpec = updSpec   (giSpec info) vs }
    updSpec   sp   vs = sp   { gsTerm = updSpTerm (gsTerm sp)   vs }
    updSpTerm gsT  vs = gsT  { gsNonStTerm = S.fromList vs         } 
      

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

instance Show Cinfo where
  show = show . F.toFix

solveCs :: Config -> FilePath -> CGInfo -> GhcInfo -> Maybe [String] -> IO (Output Doc)
solveCs cfg tgt cgi info names = do
  finfo            <- cgInfoFInfo info cgi
  F.Result r sol _ <- solve (fixConfig tgt cfg) finfo
  let resErr        = applySolution sol . cinfoError . snd <$> r
  -- resModel_        <- fmap (e2u cfg sol) <$> getModels info cfg resErr
  let resModel_     = e2u cfg sol <$> resErr
  let resModel      = resModel_  `addErrors` (e2u cfg sol <$> logErrors cgi)
  let out0          = mkOutput cfg resModel sol (annotMap cgi)
  return            $ out0 { o_vars    = names    }
                           { o_result  = resModel }

e2u :: Config -> F.FixSolution -> Error -> UserError
e2u cfg s = fmap F.pprint . tidyError cfg s

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
