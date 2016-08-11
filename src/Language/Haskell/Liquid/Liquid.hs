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
  ) where

import           Prelude hiding (error)
import           Data.Bifunctor
import           Data.Maybe
import           System.Exit
import           Text.PrettyPrint.HughesPJ
-- import           Var                              (Var)
import           CoreSyn
import           HscTypes                         (SourceError)
import           GHC (HscEnv)
import           System.Console.CmdArgs.Verbosity (whenLoud, whenNormal)
import           System.Console.CmdArgs.Default
import           Control.Monad (when)
import qualified Control.Exception as Ex
import qualified Language.Fixpoint.Types.Config as FC
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
import           Language.Haskell.Liquid.GHC.Misc (showCBs) -- howPpr)
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Model
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
  z <- actOrDie $ second Just <$> getGhcInfo mE cfg (files cfg)
  case z of
    Left e -> do
      exitWithResult cfg (files cfg) $ mempty { o_result = e }
      return (resultExit e, mE)
    Right (gs, mE') -> do
      d <- checkMany cfg mempty gs
      return (ec d, mE')
  where
    ec = resultExit . o_result

------------------------------------------------------------------------------
checkMany :: Config -> Output Doc -> [GhcInfo] -> IO (Output Doc)
------------------------------------------------------------------------------
checkMany cfg d (g:gs) = do
  d' <- checkOne cfg g
  checkMany cfg (d `mappend` d') gs

checkMany _   d [] =
  return d

------------------------------------------------------------------------------
checkOne :: Config -> GhcInfo -> IO (Output Doc)
------------------------------------------------------------------------------
checkOne cfg g = do
  z <- actOrDie $ liquidOne g
  case z of
    Left  e -> exitWithResult cfg [target g] $ mempty { o_result = e }
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

------------------------------------------------------------------------------
liquidOne :: GhcInfo -> IO (Output Doc)
------------------------------------------------------------------------------
liquidOne info = do
  whenNormal $ donePhase Loud "Extracted Core using GHC"
  let cfg   = getConfig info
  let tgt   = target info
  -- whenLoud  $ do putStrLn $ showpp info
                 -- putStrLn "*************** Original CoreBinds ***************************"
                 -- putStrLn $ render $ pprintCBs (cbs info)
  let cbs' = transformScope (cbs info)
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

newPrune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Either [CoreBind] [DC.DiffCheck])
newPrune cfg cbs tgt info
  | not (null vs) = return . Right $ [DC.thin cbs sp vs]
  | timeBinds cfg = return . Right $ [DC.thin cbs sp [v] | v <- exportedVars info ]
  | diffcheck cfg = maybeEither cbs <$> DC.slice tgt cbs sp
  | otherwise     = return  (Left cbs)
  where
    vs            = gsTgtVars sp
    sp            = spec    info

-- topLevelBinders :: GhcSpec -> [Var]
-- topLevelBinders = map fst . tySigs

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
  when False (dumpCs cgi)
  -- whenLoud $ mapM_ putStrLn [ "****************** CGInfo ********************"
                            -- , render (pprint cgi)                            ]
  out   <- timedAction names $ solveCs cfg tgt cgi info' names
  return $  mconcat [oldOut, out]
  where
    cgi    = {-# SCC "generateConstraints" #-} generateConstraints $! info' {cbs = cbs''}
    cbs''  = either id              DC.newBinds                        edc
    info'  = either (const info)    (\z -> info {spec = DC.newSpec z}) edc
    names  = either (const Nothing) (Just . map show . DC.checkedVars) edc
    oldOut = either (const mempty)  DC.oldOutput                       edc


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


solveCs :: Config -> FilePath -> CGInfo -> GhcInfo -> Maybe [String] -> IO (Output Doc)
solveCs cfg tgt cgi info names = do
  finfo          <- cgInfoFInfo info cgi tgt
  F.Result r sol <- solve (fixConfig tgt cfg) finfo
  let resErr      = applySolution sol . cinfoError . snd <$> r
  resModel_      <- fmap (e2u sol) <$> getModels info cfg resErr
  let resModel    = resModel_  `addErrors` (e2u sol <$> logErrors cgi)
  let out0        = mkOutput cfg resModel sol (annotMap cgi)
  return          $ out0 { o_vars    = names    }
                         { o_result  = resModel }

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = def
  { FC.solver      = fromJust (smtsolver cfg)
  , FC.linear      = linear            cfg
  , FC.eliminate   = not $ noEliminate cfg
  --, FC.oldElim     = True -- oldEliminate      cfg
  --, FC.pack        = packKVars cfg
  , FC.nonLinCuts  = True -- nonLinCuts        cfg
  , FC.save        = saveQuery         cfg
  , FC.srcFile     = tgt
  , FC.cores       = cores             cfg
  , FC.minPartSize = minPartSize       cfg
  , FC.maxPartSize = maxPartSize       cfg
  , FC.elimStats   = elimStats         cfg
  , FC.elimBound   = elimBound         cfg
  , FC.allowHO     = higherOrderFlag   cfg
  , FC.allowHOqs   = higherorderqs     cfg

  , FC.extensionality   = extensionality   cfg
  , FC.alphaEquivalence = alphaEquivalence cfg
  , FC.betaEquivalence  = betaEquivalence  cfg
  , FC.normalForm       = normalForm       cfg
  , FC.stringTheory     = stringTheory     cfg 
  }

e2u :: F.FixSolution -> Error -> UserError
e2u s = fmap F.pprint . tidyError s

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
