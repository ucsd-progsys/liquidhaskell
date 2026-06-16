{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--diff"     @-}

module Language.Haskell.Liquid.Liquid (
   -- * Checking a single module
    checkTargetInfo
  ) where

import           Prelude hiding (error)
import           Data.Bifunctor
import qualified Data.HashSet as S
import           Text.PrettyPrint.HughesPJ
import           Control.Monad (when)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Mb
import qualified Data.List  as L
import qualified Language.Haskell.Liquid.UX.DiffCheck as DC
import           Language.Haskell.Liquid.Misc
import qualified Language.Fixpoint.Misc as F
import           Language.Fixpoint.Solver
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.GHC.Misc (showCBs, ignoreCoreBinds) -- howPpr)
import           Language.Haskell.Liquid.Constraint.Generate
import           Language.Haskell.Liquid.Constraint.ToFixpoint
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.UX.Annotate (mkOutput)
import qualified Language.Haskell.Liquid.Termination.Structural as ST
import qualified Language.Haskell.Liquid.GHC.Misc          as GM
import           Liquid.GHC.API as GHC hiding (text, vcat, ($+$), (<+>))
import Language.Haskell.Liquid.Types.RType (SpecType)

-- Second output is intended for Refcore
--------------------------------------------------------------------------------
checkTargetInfo :: TargetInfo -> IO (Output Doc, AnnInfo SpecType)
--------------------------------------------------------------------------------
checkTargetInfo info = do
  (out, infTypes) <- check
  when (diffcheck cfg && not (compileSpec cfg)) $ DC.saveResult tgt out
  pure (out, infTypes)
  where
    check :: IO (Output Doc, AnnInfo SpecType)
    check
      | compileSpec cfg = do
        -- donePhase Loud "Only compiling specifications [skipping verification]"
        pure (mempty { o_result = F.Safe mempty }, mempty)
      | otherwise = do
        when (loggingVerbosity cfg == Normal) $ do
          F.donePhase F.Loud "Extracted Core using GHC"
          F.donePhase F.Loud "Transformed Core"
        when (loggingVerbosity cfg == Loud) $ do
          F.donePhase F.Loud "transformRecExpr-1773-hoho"
          putStrLn "*************** Transform Rec Expr CoreBinds *****************"
          putStrLn $ showCBs (untidyCore cfg) cbs'
        edcs <- newPrune cfg cbs' tgt info
        liquidQueries cfg tgt info edcs

    cfg :: Config
    cfg  = getConfig info

    tgt :: FilePath
    tgt  = giTarget (giSrc info)

    cbs' :: [CoreBind]
    cbs' = giCbs (giSrc info)

newPrune :: Config -> [CoreBind] -> FilePath -> TargetInfo -> IO (Either [CoreBind] [DC.DiffCheck])
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

exportedVars :: TargetSrc -> [Var]
exportedVars src = filter (isExportedVar src) (giDefVars src)

maybeEither :: a -> Maybe b -> Either a [b]
maybeEither d Nothing  = Left d
maybeEither _ (Just x) = Right [x]

liquidQueries :: Config -> FilePath -> TargetInfo -> Either [CoreBind] [DC.DiffCheck] -> IO (Output Doc, AnnInfo SpecType)
liquidQueries cfg tgt info (Left cbs')
  = liquidQuery cfg tgt info (Left cbs')
liquidQueries cfg tgt info (Right dcs)
  = mconcat <$> mapM (liquidQuery cfg tgt info . Right) dcs

liquidQuery   :: Config -> FilePath -> TargetInfo -> Either [CoreBind] DC.DiffCheck -> IO (Output Doc, AnnInfo SpecType)
liquidQuery cfg tgt info edc = do
  let names   = either (const Nothing) (Just . map show . DC.checkedVars)   edc
  let oldOut  = either (const mempty)  DC.oldOutput                         edc
  let info1   = either (const info)    (\z -> info {giSpec = DC.newSpec z}) edc
  let cbs''   = either id              DC.newBinds                          edc
  let info2   = info1 { giSrc = (giSrc info1) {giCbs = cbs''}}
  let info3   = updTargetInfoTermVars info2
  let cgi     = {-# SCC "generateConstraints" #-} generateConstraints $! info3
  when False (dumpCs cgi)
  -- whenLoud $ mapM_ putStrLn [ "****************** CGInfo ********************"
                            -- , render (pprint cgi)                            ]
  out        <- timedAction names $ solveCs cfg tgt cgi info3 names
  return      $ mconcat [(oldOut, mempty), out]

updTargetInfoTermVars    :: TargetInfo -> TargetInfo
updTargetInfoTermVars i  = updInfo i  (ST.terminationVars i)
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

solveCs :: Config -> FilePath -> CGInfo -> TargetInfo -> Maybe [String] -> IO (Output Doc, AnnInfo SpecType)
solveCs cfg tgt cgi info names = do
  finfo            <- cgInfoFInfo info cgi
  let fcfg          = fixConfig tgt cfg
  F.Result {resStatus=r0, resSolution=solCuts, resNonCutsSolution=solNonCuts} <- solve fcfg finfo
  let sol           = HashMap.union (HashMap.map F.Delayed solCuts) solNonCuts
  let failBs        = gsFail $ gsTerm $ giSpec info
  let (r,rf)        = splitFails (S.map val failBs) r0
  let resErr        = second (applySolution finfo sol . cinfoError) <$> r
  -- resModel_        <- fmap (e2u cfg sol) <$> getModels info cfg resErr
  let resModel_     = cidE2u cfg <$> resErr
  let resModel'     = resModel_  `addErrors` (e2u cfg <$> logErrors cgi)
                                 `addErrors` makeFailErrors (S.toList failBs) rf
                                 `addErrors` makeFailUseErrors (S.toList failBs) (giCbs $ giSrc info)
  let lErrors       = applySolution finfo sol <$> logErrors cgi
  let resModel      = resModel' `addErrors` (e2u cfg <$> lErrors)
  let (out0, infTypes) = mkOutput cfg resModel finfo sol (annotMap cgi)
  return (out0 { o_vars    = names    } { o_result  = resModel }, infTypes)


e2u :: Config -> Error -> UserError
e2u cfg = fmap F.pprint . tidyError cfg

cidE2u :: Config -> (Integer, Error) -> UserError
cidE2u cfg (subcId, e) =
  let e' = attachSubcId e
   in fmap F.pprint (tidyError cfg e')
  where
    attachSubcId es@ErrSubType{}      = es { cid = Just subcId }
    attachSubcId es@ErrSubTypeModel{} = es { cid = Just subcId }
    attachSubcId es@ErrAssType{}      = es { cid = Just subcId }
    attachSubcId es = es

-- writeCGI tgt cgi = {-# SCC "ConsWrite" #-} writeFile (extFileName Cgi tgt) str
--   where
--     str          = {-# SCC "PPcgi" #-} showpp cgi


makeFailUseErrors :: [F.Located Var] -> [CoreBind] -> [UserError]
makeFailUseErrors fbs cbs = [ mkError x bs | x <- fbs
                                          , let bs = clients (val x)
                                          , not (null bs) ]
  where
    mkError x bs = ErrFailUsed (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (pprint <$> bs)
    clients x    = map fst $ filter (elem x . snd) allClients

    allClients = concatMap go cbs

    go :: CoreBind -> [(Var,[Var])]
    go (NonRec x e) = [(x, readVars e)]
    go (Rec xes)    = [(x,cls) | x <- map fst xes] where cls = concatMap (readVars . snd) xes

makeFailErrors :: [F.Located Var] -> [Cinfo] -> [UserError]
makeFailErrors bs cis = [ mkError x | x <- bs, notElem (val x) vs ]
  where
    mkError  x = ErrFail (GM.sourcePosSrcSpan $ loc x) (pprint $ val x)
    vs         = Mb.mapMaybe ci_var cis

splitFails :: S.HashSet Var -> F.FixResult (a, Cinfo) -> (F.FixResult (a, Cinfo),  [Cinfo])
splitFails _ r@(F.Crash _ _) = (r,mempty)
splitFails _ r@(F.Safe _)    = (r,mempty)
splitFails fs (F.Unsafe s xs)  = (mkRes r, snd <$> rfails)
  where
    (rfails,r) = L.partition (Mb.maybe False (`S.member` fs) . ci_var . snd) xs
    mkRes [] = F.Safe s
    mkRes ys = F.Unsafe s ys

