-- | This module provides a GHC 'Plugin' that allows LiquidHaskell to be hooked directly into GHC's
-- compilation pipeline, facilitating its usage and adoption.

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ViewPatterns               #-}

module Language.Haskell.Liquid.GHC.Plugin (

  plugin

  ) where

import qualified Language.Haskell.Liquid.GHC.API         as O
import           Language.Haskell.Liquid.GHC.API         as GHC hiding (Target, Type)
import qualified Text.PrettyPrint.HughesPJ               as PJ
import qualified Language.Fixpoint.Types                 as F
import qualified Language.Haskell.Liquid.GHC.Misc        as LH
import qualified Language.Haskell.Liquid.UX.CmdLine      as LH
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import qualified Language.Haskell.Liquid.Liquid          as LH
import qualified Language.Haskell.Liquid.Types.PrettyPrint as LH ( filterReportErrors
                                                                 , filterReportErrorsWith
                                                                 , defaultFilterReporter
                                                                 , reduceFilters )
import qualified Language.Haskell.Liquid.GHC.Logging     as LH   (fromPJDoc)

import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.GHC.Plugin.Util as Util
import           Language.Haskell.Liquid.GHC.Plugin.SpecFinder
                                                         as SpecFinder

import           Language.Haskell.Liquid.GHC.Types       (MGIModGuts(..), miModGuts)
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike
                                                         as GhcMonadLike
import           Language.Haskell.Liquid.GHC.GhcMonadLike ( GhcMonadLike
                                                          , askHscEnv
                                                          , isBootInterface
                                                          )
import           GHC.LanguageExtensions

import           Control.Monad

import           Data.Coerce
import           Data.Kind                                ( Type )
import           Data.List                               as L
                                                   hiding ( intersperse )
import           Data.IORef
import qualified Data.Set                                as S
import           Data.Set                                 ( Set )


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM

import           System.IO.Unsafe                         ( unsafePerformIO )
import           Language.Fixpoint.Types           hiding ( panic
                                                          , Error
                                                          , Result
                                                          , Expr
                                                          )

import qualified Language.Haskell.Liquid.Measure         as Ms
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.Transforms.ANF
import           Language.Haskell.Liquid.Types     hiding ( getConfig )
import           Language.Haskell.Liquid.Bare
import           Language.Haskell.Liquid.UX.CmdLine

import           Optics
import Data.Either (fromRight)

data LiquidCheckException =
  KillPluginWithSuccess
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- | State and configuration management -----------------------------------------
---------------------------------------------------------------------------------

-- | A reference to cache the LH's 'Config' and produce it only /once/, during the dynFlags hook.
cfgRef :: IORef Config
cfgRef = unsafePerformIO $ newIORef defConfig
{-# NOINLINE cfgRef #-}

-- | Set to 'True' to enable debug logging.
debugLogs :: Bool
debugLogs = False

---------------------------------------------------------------------------------
-- | Useful functions -----------------------------------------------------------
---------------------------------------------------------------------------------

-- | Reads the 'Config' out of a 'IORef'.
getConfig :: IO Config
getConfig = readIORef cfgRef

-- | Combinator which conditionally print on the screen based on the value of 'debugLogs'.
debugLog :: MonadIO m => String -> m ()
debugLog msg = when debugLogs $ liftIO (putStrLn msg)

---------------------------------------------------------------------------------
-- | The Plugin entrypoint ------------------------------------------------------
---------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin {
    typeCheckResultAction = liquidPlugin
  , dynflagsPlugin        = customDynFlags
  , pluginRecompile       = purePlugin
  }
  where
    -- Unfortunately, we can't make Haddock run the LH plugin, because the former
    -- does mangle the '.hi' files, causing annotations to not be persisted in the
    -- 'ExternalPackageState' and/or 'HomePackageTable'. For this reason we disable
    -- the plugin altogether is the module is being compiled with Haddock.
    -- See also: https://github.com/ucsd-progsys/liquidhaskell/issues/1727
    -- for a post-mortem.
    liquidPlugin :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
    liquidPlugin opts summary gblEnv = do
      dynFlags <- getDynFlags
      if gopt Opt_Haddock dynFlags
        then do
          -- Warn the user
          let msg     = PJ.vcat [ PJ.text "LH can't be run with Haddock."
                                , PJ.nest 4 $ PJ.text "Documentation will still be created."
                                ]
          let srcLoc  = mkSrcLoc (mkFastString $ ms_hspp_file summary) 1 1
          let warning = mkWarning (mkSrcSpan srcLoc srcLoc) msg
          liftIO $ printWarning dynFlags warning
          pure gblEnv
        else do
          newGblEnv <- typecheckHook opts summary gblEnv
          pure $ fromRight gblEnv newGblEnv

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

-- | Overrides the default 'DynFlags' options. Specifically, we need the GHC
-- lexer not to throw away block comments, as this is where the LH spec comments
-- would live. This is why we set the 'Opt_KeepRawTokenStream' option.
customDynFlags :: [CommandLineOption] -> DynFlags -> IO DynFlags
customDynFlags opts dflags = do
  cfg <- liftIO $ LH.getOpts opts
  writeIORef cfgRef cfg
  configureDynFlags dflags
  where
    configureDynFlags :: DynFlags -> IO DynFlags
    configureDynFlags df =
      pure $ df `gopt_set` Opt_ImplicitImportQualified
                `gopt_set` Opt_PIC
                `gopt_set` Opt_DeferTypedHoles
                `gopt_set` Opt_KeepRawTokenStream
                `xopt_set` MagicHash
                `xopt_set` DeriveGeneric
                `xopt_set` StandaloneDeriving

--------------------------------------------------------------------------------
-- | \"Unoptimising\" things ----------------------------------------------------
--------------------------------------------------------------------------------

-- | LiquidHaskell requires the unoptimised core binds in order to work correctly, but at the same time the
-- user can invoke GHC with /any/ optimisation flag turned out. This is why we grab the core binds by
-- desugaring the module during /parsing/ (before that's already too late) and we cache the core binds for
-- the rest of the program execution.
class Unoptimise a where
  type UnoptimisedTarget a :: Type
  unoptimise :: a -> UnoptimisedTarget a

instance Unoptimise DynFlags where
  type UnoptimisedTarget DynFlags = DynFlags
  unoptimise df = updOptLevel 0 df
    { debugLevel   = 1
    , ghcLink      = LinkInMemory
    , hscTarget    = HscInterpreted
    , ghcMode      = CompManager
    }

instance Unoptimise ModSummary where
  type UnoptimisedTarget ModSummary = ModSummary
  unoptimise modSummary = modSummary { ms_hspp_opts = unoptimise (ms_hspp_opts modSummary) }

instance Unoptimise (DynFlags, HscEnv) where
  type UnoptimisedTarget (DynFlags, HscEnv) = HscEnv
  unoptimise (unoptimise -> df, env) = env { hsc_dflags = df }

--------------------------------------------------------------------------------
-- | Typechecking phase --------------------------------------------------------
--------------------------------------------------------------------------------

-- | We hook at this stage of the pipeline in order to call \"liquidhaskell\". This
-- might seems counterintuitive as LH works on a desugared module. However, there
-- are a bunch of reasons why we do this:
--
-- 1. Tools like \"ghcide\" works by running the compilation pipeline up until
--    this stage, which means that we won't be able to report errors and warnings
--    if we call /LH/ any later than here;
--
-- 2. Although /LH/ works on \"Core\", it requires the _unoptimised_ \"Core\" that we
--    grab from parsing (again) the module by using the GHC API, so we are really
--    independent from the \"normal\" compilation pipeline.
--
typecheckHook :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM (Either LiquidCheckException TcGblEnv)
typecheckHook _ (unoptimise -> modSummary) tcGblEnv = do
  debugLog $ "We are in module: " <> show (toStableModule thisModule)

  parsed        <- GhcMonadLike.parseModule (LH.keepRawTokenStream cleanedSummary)
  let comments  = LH.extractSpecComments (pm_annotations parsed)
  typechecked     <- GhcMonadLike.typecheckModule (LH.ignoreInline parsed)
  env             <- askHscEnv
  resolvedNames   <- LH.lookupTyThings env modSummary tcGblEnv
  availTyCons     <- LH.availableTyCons env modSummary tcGblEnv (tcg_exports tcGblEnv)
  availVars       <- LH.availableVars env modSummary tcGblEnv (tcg_exports tcGblEnv)

  unoptimisedGuts <- GhcMonadLike.desugarModule modSummary typechecked

  let tcData = mkTcData (tcg_rn_imports tcGblEnv) resolvedNames availTyCons availVars
  let pipelineData = PipelineData (toUnoptimised unoptimisedGuts) tcData (map SpecComment comments)

  liquidHaskellCheck pipelineData modSummary tcGblEnv

  where
    thisModule :: Module
    thisModule = tcg_mod tcGblEnv

    cleanedSummary :: ModSummary
    cleanedSummary =
        modSummary { ms_hspp_opts = (ms_hspp_opts modSummary) { cachedPlugins = []
                                                              , staticPlugins = []
                                                              }
                   }

serialiseSpec :: Module -> TcGblEnv -> LiquidLib -> TcM TcGblEnv
serialiseSpec thisModule tcGblEnv liquidLib = do
  -- ---
  -- -- CAN WE 'IGNORE' THE BELOW? TODO:IGNORE -- issue use `emptyLiquidLib` instead of pmrClientLib
  -- ProcessModuleResult{..} <- processModule lhContext

  -- liftIO $ putStrLn "liquidHaskellCheck 7"

  -- -- Call into the existing Liquid interface
  -- out <- liftIO $ LH.checkTargetInfo pmrTargetInfo

  -- liftIO $ putStrLn "liquidHaskellCheck 8"

  -- -- Report the outcome of the checking
  -- LH.reportResult errorLogger cfg [giTarget (giSrc pmrTargetInfo)] out
  -- case o_result out of
  --   Safe _stats -> pure ()
  --   _           -> failM

  -- liftIO $ putStrLn "liquidHaskellCheck 9"
  -- ---

  let serialisedSpec = Util.serialiseLiquidLib liquidLib thisModule
  debugLog $ "Serialised annotation ==> " ++ (O.showSDocUnsafe . O.ppr $ serialisedSpec)

  -- liftIO $ putStrLn "liquidHaskellCheck 10"

  pure $ tcGblEnv { tcg_anns = serialisedSpec : tcg_anns tcGblEnv }

processInputSpec :: Config -> PipelineData -> ModSummary -> TcGblEnv -> BareSpec -> TcM (Either LiquidCheckException TcGblEnv)
processInputSpec cfg pipelineData modSummary tcGblEnv inputSpec = do
  debugLog $ " Input spec: \n" ++ show inputSpec
  debugLog $ "Relevant ===> \n" ++ unlines (renderModule <$> S.toList (relevantModules modGuts))

  logicMap :: LogicMap <- liftIO LH.makeLogicMap

  -- debugLog $ "Logic map:\n" ++ show logicMap

  let lhContext = LiquidHaskellContext {
        lhGlobalCfg       = cfg
      , lhInputSpec       = inputSpec
      , lhModuleLogicMap  = logicMap
      , lhModuleSummary   = modSummary
      , lhModuleTcData    = pdTcData pipelineData
      , lhModuleGuts      = pdUnoptimisedCore pipelineData
      , lhRelevantModules = relevantModules modGuts
      }

  -- liftIO $ putStrLn ("liquidHaskellCheck 6: " ++ show isIg)
  liquidLib' :: Either LiquidCheckException LiquidLib <-
    if isIgnore inputSpec
    then pure $ Right emptyLiquidLib
    else checkLiquidHaskellContext lhContext

  traverse (serialiseSpec thisModule tcGblEnv) liquidLib'

  where
    thisModule :: Module
    thisModule = tcg_mod tcGblEnv

    modGuts :: ModGuts
    modGuts = fromUnoptimised . pdUnoptimisedCore $ pipelineData

liquidHaskellCheckWithConfig :: Config -> PipelineData -> ModSummary -> TcGblEnv -> TcM (Either LiquidCheckException TcGblEnv)
liquidHaskellCheckWithConfig cfg pipelineData modSummary tcGblEnv = do
  -- The 'specQuotes' contain stuff we need from imported modules, extracted
  -- from the annotations in their interface files.
  let specQuotes :: [BPspec]
      specQuotes = LH.extractSpecQuotes' tcg_mod tcg_anns tcGblEnv

      thisFile :: FilePath
      thisFile = LH.modSummaryHsFile modSummary


  -- Here, we are calling Liquid Haskell's parser, acting on the unparsed
  -- spec comments stored in the pipeline data, supported by the specQuotes
  -- obtained from the imported modules.
  inputSpec' :: Either LiquidCheckException BareSpec <-
    getLiquidSpec thisFile thisModule (pdSpecComments pipelineData) specQuotes

  join <$> traverse (processInputSpec cfg pipelineData modSummary tcGblEnv) inputSpec'

  where
    thisModule :: Module
    thisModule = tcg_mod tcGblEnv

-- | Partially calls into LiquidHaskell's GHC API.
liquidHaskellCheck :: PipelineData -> ModSummary -> TcGblEnv -> TcM (Either LiquidCheckException TcGblEnv)
liquidHaskellCheck pipelineData modSummary tcGblEnv = do
  cfg <- liftIO getConfig
  liquidHaskellCheckWithConfig cfg pipelineData modSummary tcGblEnv
    `gcatch` (\(e :: UserError) -> reportErrs cfg [e])
    `gcatch` (\(e :: Error) -> reportErrs cfg [e])
    `gcatch` (\(es :: [Error]) -> reportErrs cfg es)
  where
    file :: FilePath
    file = LH.modSummaryHsFile modSummary

    continue :: TcM (Either LiquidCheckException TcGblEnv)
    continue = pure $ Left KillPluginWithSuccess

    reportErrs :: (Show e, F.PPrint e) => Config -> [TError e] -> TcM (Either LiquidCheckException TcGblEnv)
    reportErrs cfg = LH.filterReportErrors file GHC.failM continue (getFilters cfg) Full

checkLiquidHaskellContext :: LiquidHaskellContext -> TcM (Either LiquidCheckException LiquidLib)
checkLiquidHaskellContext lhContext = do
  ProcessModuleResult{..} <- processModule lhContext

  -- Call into the existing Liquid interface
  out <- liftIO $ LH.checkTargetInfo pmrTargetInfo

  let bareSpec = lhInputSpec lhContext
      file = LH.modSummaryHsFile $ lhModuleSummary lhContext

  withPragmas (lhGlobalCfg lhContext) file (Ms.pragmas $ review bareSpecIso bareSpec) $ \moduleCfg ->  do
    let filters = getFilters moduleCfg
    -- Report the outcome of the checking
    wasUnsafeButContinued <- LH.reportResult (errorLogger file filters) moduleCfg [giTarget (giSrc pmrTargetInfo)] out
    if wasUnsafeButContinued
      then pure $ Left KillPluginWithSuccess
      else pure $ Right pmrClientLib

errorLogger :: FilePath -> [Filter] -> OutputResult -> TcM ()
errorLogger file filters outputResult = do
  LH.filterReportErrorsWith
    FilterReportErrorsArgs { msgReporter = GHC.reportErrors
                           , filterReporter = LH.defaultFilterReporter file
                           , failure = GHC.failM
                           , continue = pure ()
                           , pprinter = \(spn, e) -> mkLongErrAt spn (LH.fromPJDoc e) O.empty
                           , filterMapper = LH.reduceFilters (PJ.render . snd) filters
                           , filters = filters
                           }
    (LH.orMessages outputResult)

emptyLiquidLib :: LiquidLib
emptyLiquidLib = mkLiquidLib emptyLiftedSpec

isIgnore :: BareSpec -> Bool
isIgnore (MkBareSpec sp) = any ((== "--skip-module") . F.val) (pragmas sp)

--------------------------------------------------------------------------------
-- | Working with bare & lifted specs ------------------------------------------
--------------------------------------------------------------------------------

loadDependencies :: forall m. GhcMonadLike m
                 => Config
                 -- ^ The 'Config' associated to the /current/ module being compiled.
                 -> ExternalPackageState
                 -> HomePackageTable
                 -> Module
                 -> [Module]
                 -> m TargetDependencies
loadDependencies currentModuleConfig eps hpt thisModule mods = do
  results   <- SpecFinder.findRelevantSpecs eps hpt mods
  deps      <- foldlM processResult mempty (reverse results)
  redundant <- configToRedundantDependencies currentModuleConfig

  debugLog $ "Redundant dependencies ==> " ++ show redundant

  pure $ foldl' (flip dropDependency) deps redundant
  where
    processResult :: TargetDependencies -> SpecFinderResult -> m TargetDependencies
    processResult !acc (SpecNotFound mdl) = do
      debugLog $ "[T:" ++ renderModule thisModule
              ++ "] Spec not found for " ++ renderModule mdl
      pure acc
    processResult _ (SpecFound originalModule location _) = do
      dynFlags <- getDynFlags
      debugLog $ "[T:" ++ show (moduleName thisModule)
              ++ "] Spec found for " ++ renderModule originalModule ++ ", at location " ++ show location
      Util.pluginAbort (O.showSDoc dynFlags $ O.text "A BareSpec was returned as a dependency, this is not allowed, in " O.<+> O.ppr thisModule)
    processResult !acc (LibFound originalModule location lib) = do
      debugLog $ "[T:" ++ show (moduleName thisModule)
              ++ "] Lib found for " ++ renderModule originalModule ++ ", at location " ++ show location
      pure $ TargetDependencies {
          getDependencies = HM.insert (toStableModule originalModule) (libTarget lib) (getDependencies $ acc <> libDeps lib)
        }

-- | The collection of dependencies and usages modules which are relevant for liquidHaskell
relevantModules :: ModGuts -> Set Module
relevantModules modGuts = used `S.union` dependencies
  where
    dependencies :: Set Module
    dependencies = S.fromList $ map (toModule . gwib_mod)
                              . filter (not . isBootInterface . gwib_isBoot)
                              . getDependenciesModuleNames $ deps

    deps :: Dependencies
    deps = mg_deps modGuts

    thisModule :: Module
    thisModule = mg_module modGuts

    toModule :: ModuleName -> Module
    toModule = unStableModule . mkStableModule (moduleUnitId thisModule)

    used :: Set Module
    used = S.fromList $ foldl' collectUsage mempty . mg_usages $ modGuts
      where
        collectUsage :: [Module] -> Usage -> [Module]
        collectUsage acc = \case
          UsagePackageModule     { usg_mod      = modl    } -> modl : acc
          UsageHomeModule        { usg_mod_name = modName } -> toModule modName : acc
          UsageMergedRequirement { usg_mod      = modl    } -> modl : acc
          _ -> acc


data LiquidHaskellContext = LiquidHaskellContext {
    lhGlobalCfg        :: Config
  , lhInputSpec        :: BareSpec
  , lhModuleLogicMap   :: LogicMap
  , lhModuleSummary    :: ModSummary
  , lhModuleTcData     :: TcData
  , lhModuleGuts       :: Unoptimised ModGuts
  , lhRelevantModules  :: Set Module
  }

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

data ProcessModuleResult = ProcessModuleResult {
    pmrClientLib  :: LiquidLib
  -- ^ The \"client library\" we will serialise on disk into an interface's 'Annotation'.
  , pmrTargetInfo :: TargetInfo
  -- ^ The 'GhcInfo' for the current 'Module' that LiquidHaskell will process.
  }

-- | Parse the spec comments from one module, supported by the
-- spec quotes from the imported module. Also looks for
-- "companion specs" for the current module and merges them in
-- if it finds one.
getLiquidSpec :: FilePath -> Module -> [SpecComment] -> [BPspec] -> TcM (Either LiquidCheckException BareSpec)
getLiquidSpec thisFile thisModule specComments specQuotes = do
  filters <- getFilters <$> liftIO getConfig
  let commSpecE :: Either [Error] (ModName, Spec LocBareType LocSymbol)
      commSpecE = hsSpecificationP (moduleName thisModule) (coerce specComments) specQuotes
  case commSpecE of
    Left errors -> do
      LH.filterReportErrors thisFile GHC.failM continue filters Full errors
    Right (view bareSpecIso . snd -> commSpec) -> do
      res <- SpecFinder.findCompanionSpec thisModule
      case res of
        SpecFound _ _ companionSpec -> do
          debugLog $ "Companion spec found for " ++ renderModule thisModule
          pure $ Right $ commSpec <> companionSpec
        _ -> pure $ Right commSpec

  where
    continue = pure $ Left KillPluginWithSuccess

processModule :: LiquidHaskellContext -> TcM ProcessModuleResult
processModule LiquidHaskellContext{..} = do
  debugLog ("Module ==> " ++ renderModule thisModule)
  hscEnv              <- askHscEnv

  let bareSpec        = lhInputSpec
  -- /NOTE/: For the Plugin to work correctly, we shouldn't call 'canonicalizePath', because otherwise
  -- this won't trigger the \"external name resolution\" as part of 'Language.Haskell.Liquid.Bare.Resolve'
  -- (cfr. 'allowExtResolution').
  let file            = LH.modSummaryHsFile lhModuleSummary

  _                   <- LH.checkFilePragmas $ Ms.pragmas (review bareSpecIso bareSpec)

  withPragmas lhGlobalCfg file (Ms.pragmas $ review bareSpecIso bareSpec) $ \moduleCfg -> do
    eps                 <- liftIO $ readIORef (hsc_EPS hscEnv)

    dependencies       <- loadDependencies moduleCfg
                                           eps
                                           (hsc_HPT hscEnv)
                                           thisModule
                                           (S.toList lhRelevantModules)

    debugLog $ "Found " <> show (HM.size $ getDependencies dependencies) <> " dependencies:"
    when debugLogs $
      forM_ (HM.keys . getDependencies $ dependencies) $ debugLog . moduleStableString . unStableModule

    debugLog $ "mg_exports => " ++ (O.showSDocUnsafe $ O.ppr $ mg_exports modGuts)
    debugLog $ "mg_tcs => " ++ (O.showSDocUnsafe $ O.ppr $ mg_tcs modGuts)

    targetSrc  <- makeTargetSrc moduleCfg file lhModuleTcData modGuts hscEnv
    dynFlags <- getDynFlags

    -- See https://github.com/ucsd-progsys/liquidhaskell/issues/1711
    -- Due to the fact the internals can throw exceptions from pure code at any point, we need to
    -- call 'evaluate' to force any exception and catch it, if we can.


    result <-
      makeTargetSpec moduleCfg lhModuleLogicMap targetSrc bareSpec dependencies

    let filters = getFilters moduleCfg
        emptyTargetSpec =
          TargetSpec
            mempty
            (SpQual mempty mempty)
            (SpData mempty mempty mempty mempty mempty mempty)
            (SpNames mempty mempty mempty mempty mempty (TyConMap mempty mempty mempty))
            mempty
            mempty
            mempty
            (SpLaws mempty mempty)
            mempty
            moduleCfg
        continue = pure $ ProcessModuleResult emptyLiquidLib (TargetInfo targetSrc emptyTargetSpec)
        reportErrs :: (Show e, F.PPrint e) => [TError e] -> TcRn ProcessModuleResult
        reportErrs = LH.filterReportErrors file GHC.failM continue filters Full

    (case result of
      -- Print warnings and errors, aborting the compilation.
      Left diagnostics -> do
        liftIO $ mapM_ (printWarning dynFlags)    (allWarnings diagnostics)
        LH.filterReportErrors file GHC.failM continue filters Full (allErrors diagnostics)
      Right (warnings, targetSpec, liftedSpec) -> do
        liftIO $ mapM_ (printWarning dynFlags) warnings
        let targetInfo = TargetInfo targetSrc targetSpec

        debugLog $ "bareSpec ==> "   ++ show bareSpec
        debugLog $ "liftedSpec ==> " ++ show liftedSpec

        let clientLib  = mkLiquidLib liftedSpec & addLibDependencies dependencies

        let result' = ProcessModuleResult {
              pmrClientLib  = clientLib
            , pmrTargetInfo = targetInfo
            }

        pure result')
      `gcatch` (\(e :: UserError) -> reportErrs [e])
      `gcatch` (\(e :: Error) -> reportErrs [e])
      `gcatch` (\(es :: [Error]) -> reportErrs es)

  where
    modGuts    = fromUnoptimised lhModuleGuts
    thisModule = mg_module modGuts

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen
---------------------------------------------------------------------------------------

makeTargetSrc :: GhcMonadLike m
              => Config
              -> FilePath
              -> TcData
              -> ModGuts
              -> HscEnv
              -> m TargetSrc
makeTargetSrc cfg file tcData modGuts hscEnv = do
  coreBinds      <- liftIO $ anormalize cfg hscEnv modGuts

  -- The type constructors for a module are the (nubbed) union of the ones defined and
  -- the ones exported. This covers the case of \"wrapper modules\" that simply re-exports
  -- everything from the imported modules.
  let availTcs    = tcAvailableTyCons tcData
  let allTcs      = L.nub $ (mgi_tcs mgiModGuts ++ availTcs)

  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) allTcs
  let (fiTcs, fiDcs) = LH.makeFamInstEnv (getFamInstances modGuts)
  let things         = tcResolvedNames tcData
  let impVars        = LH.importVars coreBinds ++ LH.classCons (mgi_cls_inst mgiModGuts)

  debugLog $ "_gsTcs   => " ++ show allTcs
  debugLog $ "_gsFiTcs => " ++ show fiTcs
  debugLog $ "_gsFiDcs => " ++ show fiDcs
  debugLog $ "dataCons => " ++ show dataCons
  debugLog $ "coreBinds => " ++ (O.showSDocUnsafe . O.ppr $ coreBinds)
  debugLog $ "impVars => " ++ (O.showSDocUnsafe . O.ppr $ impVars)
  debugLog $ "defVars  => " ++ show (L.nub $ dataCons ++ letVars coreBinds ++ tcAvailableVars tcData)
  debugLog $ "useVars  => " ++ (O.showSDocUnsafe . O.ppr $ readVars coreBinds)
  debugLog $ "derVars  => " ++ (O.showSDocUnsafe . O.ppr $ HS.fromList (LH.derivedVars cfg mgiModGuts))
  debugLog $ "gsExports => " ++ show (mgi_exports  mgiModGuts)
  debugLog $ "gsTcs     => " ++ (O.showSDocUnsafe . O.ppr $ allTcs)
  debugLog $ "gsCls     => " ++ (O.showSDocUnsafe . O.ppr $ mgi_cls_inst mgiModGuts)
  debugLog $ "gsFiTcs   => " ++ (O.showSDocUnsafe . O.ppr $ fiTcs)
  debugLog $ "gsFiDcs   => " ++ show fiDcs
  debugLog $ "gsPrimTcs => " ++ (O.showSDocUnsafe . O.ppr $ GHC.primTyCons)
  debugLog $ "things   => " ++ (O.showSDocUnsafe . O.vcat . map O.ppr $ things)
  debugLog $ "allImports => " ++ (show $ tcAllImports tcData)
  debugLog $ "qualImports => " ++ (show $ tcQualifiedImports tcData)

  return $ TargetSrc
    { giIncDir    = mempty
    , giTarget    = file
    , giTargetMod = ModName Target (moduleName (mg_module modGuts))
    , giCbs       = coreBinds
    , giImpVars   = impVars
    , giDefVars   = L.nub $ dataCons ++ letVars coreBinds ++ tcAvailableVars tcData
    , giUseVars   = readVars coreBinds
    , giDerVars   = HS.fromList (LH.derivedVars cfg mgiModGuts)
    , gsExports   = mgi_exports  mgiModGuts
    , gsTcs       = allTcs
    , gsCls       = mgi_cls_inst mgiModGuts
    , gsFiTcs     = fiTcs
    , gsFiDcs     = fiDcs
    , gsPrimTcs   = GHC.primTyCons
    , gsQualImps  = tcQualifiedImports tcData
    , gsAllImps   = tcAllImports       tcData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }
  where
    mgiModGuts :: MGIModGuts
    mgiModGuts = miModGuts deriv modGuts
      where
        deriv   = Just $ instEnvElts $ mg_inst_env modGuts

getFamInstances :: ModGuts -> [FamInst]
getFamInstances guts = famInstEnvElts (mg_fam_inst_env guts)
