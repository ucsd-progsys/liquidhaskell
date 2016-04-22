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
import           Language.Haskell.Liquid.Misc
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType (applySolution)
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Tidy
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
  -- whenLoud  $ do putStrLn $ showpp info
                 -- putStrLn "*************** Original CoreBinds ***************************"
                 -- putStrLn $ render $ pprintCBs (cbs info)
  let cbs' = transformScope (cbs info)
  -- whenLoud  $ do donePhase Loud "transformRecExpr"
                 -- putStrLn "*************** Transform Rec Expr CoreBinds *****************"
                 -- putStrLn $ render $ pprintCBs cbs'
  edcs <- newPrune      cfg cbs' tgt info
  out' <- liquidQueries cfg      tgt info edcs
  DC.saveResult      tgt out'
  exitWithResult cfg tgt out'

newPrune :: Config -> [CoreBind] -> FilePath -> GhcInfo -> IO (Either [CoreBind] [DC.DiffCheck])
newPrune cfg cbs tgt info
  | not (null vs) = return . Right $ [varsQuery cbs sp vs]
  | timeBinds cfg = return . Right $ [varsQuery cbs sp [x] | (x, _) <- tySigs sp ]
  | diffcheck cfg = maybeEither cbs <$> DC.slice tgt cbs sp
  | otherwise     = return  (Left cbs)
  where
    vs            = tgtVars sp
    sp            = spec    info

varsQuery :: [CoreBind] ->  GhcSpec -> [Var] ->DC.DiffCheck
varsQuery cbs sp vs = DC.DC (DC.thin cbs vs) mempty sp

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
  whenLoud (dumpCs cgi)
  out   <- timedAction (show names) $ solveCs cfg tgt cgi info' names
  return $ mconcat [oldOut, out]
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
solveCs cfg tgt cgi info names
  = do finfo          <- cgInfoFInfo info cgi tgt
       F.Result r sol <- solve fx finfo
       let warns = logErrors cgi
       let annm  = annotMap cgi
       let res_err = fmap (applySolution sol . cinfoError . snd) r
       res_model  <- fmap (fmap pprint . tidyError sol)
                      <$> getModels info cfg res_err
       let out0  = mkOutput cfg res_model sol annm
       return    $ out0 { o_vars    = names             }
                        { o_errors  = e2u sol <$> warns }
                        { o_result  = res_model         }
    where
       fx        = def { FC.solver      = fromJust (smtsolver cfg)
                       , FC.linear      = linear      cfg
                       , FC.newcheck    = newcheck    cfg
                       , FC.eliminate   = eliminate   cfg
                       , FC.save        = saveQuery cfg
                       , FC.srcFile     = tgt
                       , FC.cores       = cores       cfg
                       , FC.minPartSize = minPartSize cfg
                       , FC.maxPartSize = maxPartSize cfg
                       , FC.elimStats   = elimStats   cfg
                       }


e2u :: F.FixSolution -> Error -> UserError
e2u s = fmap F.pprint . tidyError s

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi
