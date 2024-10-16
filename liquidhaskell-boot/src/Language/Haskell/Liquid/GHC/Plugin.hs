-- | This module provides a GHC 'Plugin' that allows LiquidHaskell to be hooked directly into GHC's
-- compilation pipeline, facilitating its usage and adoption.

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE LambdaCase                 #-}

module Language.Haskell.Liquid.GHC.Plugin (

  plugin

  ) where

import qualified Liquid.GHC.API         as O
import           Liquid.GHC.API         as GHC hiding (Type)
import qualified Text.PrettyPrint.HughesPJ               as PJ
import qualified Language.Fixpoint.Types                 as F
import qualified  Language.Haskell.Liquid.GHC.Misc        as LH
import qualified Language.Haskell.Liquid.UX.CmdLine      as LH
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import qualified Language.Haskell.Liquid.Liquid          as LH
import qualified Language.Haskell.Liquid.Types.PrettyPrint as LH ( filterReportErrors
                                                                 , filterReportErrorsWith
                                                                 , defaultFilterReporter
                                                                 , reduceFilters )
import qualified Language.Haskell.Liquid.GHC.Logging     as LH   (addTcRnUnknownMessages)

import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.GHC.Plugin.Util as Util
import           Language.Haskell.Liquid.GHC.Plugin.SpecFinder
                                                         as SpecFinder

import           Language.Haskell.Liquid.GHC.Types       (MGIModGuts(..), miModGuts)
import           Language.Haskell.Liquid.Transforms.InlineAux (inlineAux)
import           Language.Haskell.Liquid.Transforms.Rewrite (rewriteBinds)

import           Control.Monad
import qualified Control.Monad.Catch as Ex
import           Control.Monad.IO.Class (MonadIO)

import           Data.Coerce
import           Data.Function                            ((&))
import qualified Data.List                               as L
import           Data.IORef
import qualified Data.Set                                as S
import           Data.Set                                 ( Set )
import qualified Data.Map                                as M
import           Data.Map                                 ( Map )


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM

import           System.IO.Unsafe                         ( unsafePerformIO )
import           Language.Fixpoint.Types           hiding ( errs
                                                          , panic
                                                          , Error
                                                          , Result
                                                          , Expr
                                                          )

import qualified Language.Haskell.Liquid.Measure         as Ms
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.Transforms.ANF
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.PrettyPrint
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.Bare
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.UX.Config

-- | Represents an abnormal but non-fatal state of the plugin. Because it is not
-- meant to escape the plugin, it is not thrown in IO but instead carried around
-- in an `Either`'s `Left` case and handled at the top level of the plugin
-- function.
newtype LiquidCheckException = ErrorsOccurred [Filter] -- Unmatched expected errors
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- | State and configuration management -----------------------------------------
---------------------------------------------------------------------------------

-- | Set to 'True' to enable debug logging.
debugLogs :: Bool
debugLogs = False

---------------------------------------------------------------------------------
-- | Useful functions -----------------------------------------------------------
---------------------------------------------------------------------------------

-- | Combinator which conditionally print on the screen based on the value of 'debugLogs'.
debugLog :: MonadIO m => String -> m ()
debugLog msg = when debugLogs $ liftIO (putStrLn msg)

---------------------------------------------------------------------------------
-- | The Plugin entrypoint ------------------------------------------------------
---------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin {
    driverPlugin          = lhDynFlags
  , parsedResultAction    = parsedHook
  , typeCheckResultAction = liquidPlugin
  , pluginRecompile       = purePlugin
  }
  where
    liquidPlugin :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
    liquidPlugin opts summary gblEnv = do
      cfg <- liftIO $ LH.getOpts opts
      if skipModule cfg then return gblEnv
      else liquidPluginGo cfg summary gblEnv

    -- Unfortunately, we can't make Haddock run the LH plugin, because the former
    -- does mangle the '.hi' files, causing annotations to not be persisted in the
    -- 'ExternalPackageState' and/or 'HomePackageTable'. For this reason we disable
    -- the plugin altogether if the module is being compiled with Haddock.
    -- See also: https://github.com/ucsd-progsys/liquidhaskell/issues/1727
    -- for a post-mortem.
    liquidPluginGo cfg summary gblEnv = do
      logger <- getLogger
      dynFlags <- getDynFlags
      withTiming logger (text "LiquidHaskell" <+> brackets (ppr $ ms_mod_name summary)) (const ()) $ do
        if gopt Opt_Haddock dynFlags
          then do
            -- Warn the user
            let msg     = PJ.vcat [ PJ.text "LH can't be run with Haddock."
                                  , PJ.nest 4 $ PJ.text "Documentation will still be created."
                                  ]
            let srcLoc  = mkSrcLoc (mkFastString $ ms_hspp_file summary) 1 1
            let warning = mkWarning (mkSrcSpan srcLoc srcLoc) msg
            liftIO $ printWarning logger warning
            pure gblEnv
          else do
            newGblEnv <- typecheckHook cfg gblEnv
            case newGblEnv of
              -- Exit with success if all expected errors were found
              Left (ErrorsOccurred []) -> pure gblEnv
              -- Exit with error if there were unmatched expected errors
              Left (ErrorsOccurred errorFilters) -> do
                defaultFilterReporter (LH.modSummaryHsFile summary) errorFilters
                failM
              Right newGblEnv' ->
                pure newGblEnv'

--------------------------------------------------------------------------------
-- | Inter-phase communication -------------------------------------------------
--------------------------------------------------------------------------------
--
-- Since we have no good way of passing extra data between different
-- phases of our plugin, we resort to leaving breadcrumbs in horrible
-- global mutable state.
--
-- Each module gets a mutable breadcrumb during compilation.
--
-- The @parseResultAction@ sets the breadcumb to @Parsed mod@.
--
-- The @typeCheckResultAction@ clears the breadcrumb on entry.
--
-- If the @typeCheckResultAction@ does not find the breadcrumb, it skips the
-- module, assuming that it has been verified already. This could happen if
-- the plugin is activated more than once on the same module (by passing
-- multiple times @-fplugin=LiquidHaskell@ to GHC).

{- HLINT ignore Breadcrumb "Use newtype instead of data" -}
  -- It's basically an accidental detail that we only have one type of
  -- breadcrumb at the moment. We don't want to use a `newtype` to
  -- avoid communicating the false intention that a breadcrumb "is" a
  -- ParsedModule
data Breadcrumb
  = Parsed ParsedModule

breadcrumbsRef :: IORef (Map Module Breadcrumb)
breadcrumbsRef = unsafePerformIO $ newIORef mempty
{-# NOINLINE breadcrumbsRef #-}

{- HLINT ignore swapBreadcrumb "Use tuple-section" -}
swapBreadcrumb :: (MonadIO m) => Module -> Maybe Breadcrumb -> m (Maybe Breadcrumb)
swapBreadcrumb mod0 new = liftIO $ atomicModifyIORef' breadcrumbsRef $ \breadcrumbs ->
  let (old, breadcrumbs') = M.alterF (\old1 -> (old1, new)) mod0 breadcrumbs
  in (breadcrumbs', old)

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

lhDynFlags :: [CommandLineOption] -> HscEnv -> IO HscEnv
lhDynFlags _ hscEnv =
    return hscEnv
      { hsc_dflags =
          hsc_dflags hscEnv
           -- Ignore-interface-pragmas need to be unset to have access to
           -- the RHS unfoldings in the `Ghc.Var`s which is
           -- needed as part of the reflection of foreign functions in the logic
           --
           -- This needs to be active before the plugin runs, so pragmas are
           -- read at the time the interface files are loaded.
           `gopt_unset` Opt_IgnoreInterfacePragmas
           -- We need the GHC lexer not to throw away block comments,
           -- as this is where the LH spec comments would live. This
           -- is why we set the 'Opt_KeepRawTokenStream' option.
           `gopt_set` Opt_KeepRawTokenStream
      }

maybeInsertBreakPoints :: Config -> DynFlags -> DynFlags
maybeInsertBreakPoints cfg dflags =
    if insertCoreBreakPoints cfg then
      -- Opt_InsertBreakpoints is used during desugaring to prevent the
      -- simple optimizer from inlining local bindings to which we might want
      -- to attach specifications.
      --
      -- https://gitlab.haskell.org/ghc/ghc/-/issues/24386
      dflags `gopt_set` Opt_InsertBreakpoints
    else
      dflags

--------------------------------------------------------------------------------
-- | \"Unoptimising\" things ----------------------------------------------------
--------------------------------------------------------------------------------

-- | LiquidHaskell requires the unoptimised core binds in order to work correctly, but at the same time the
-- user can invoke GHC with /any/ optimisation flag turned out. This is why we grab the core binds by
-- desugaring the module during /parsing/ (before that's already too late) and we cache the core binds for
-- the rest of the program execution.
unoptimiseDynFlags :: DynFlags -> DynFlags
unoptimiseDynFlags df = updOptLevel 0 df
    { debugLevel   = 1
    , ghcLink      = LinkInMemory
    , backend      = interpreterBackend
    , ghcMode      = CompManager
    }

--------------------------------------------------------------------------------
-- | Parsing phase -------------------------------------------------------------
--------------------------------------------------------------------------------

-- | We hook at this stage of the pipeline to store the parsed module
-- for later processing during typechecking:
--
-- * Comments are preserved during parsing because we turn on
--   'Opt_KeepRawTokenStream'. So we can get the /LH/ specs from there.
--
-- * The typechecker hook needs to do desugaring itself (see the
--   comment on 'typecheckHook') which requires access to a full
--   'TypecheckedModule'. Annoyingly, the typechecker hook is given
--   only a 'TcGblEnv', so we have to redo typechecking there. And
--   the input to that needs to be a 'ParsedModule'.
--
-- LH used to reparse the module in the typechecker hook, but that doesn't work when
-- the source code is not fed from a file (See #2357).
parsedHook :: [CommandLineOption] -> ModSummary -> ParsedResult -> Hsc ParsedResult
parsedHook _ ms parsedResult = do
    -- See 'Breadcrumb' for more information.
    _oldBreadcrumb <- swapBreadcrumb thisModule $ Just (Parsed parsed)
    return parsedResult
  where
    thisModule = ms_mod ms

    parsed = ParsedModule
      { pm_mod_summary = ms
      , pm_parsed_source = hpm_module . parsedResultModule $ parsedResult
      , pm_extra_src_files = hpm_src_files . parsedResultModule $ parsedResult
      }


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
--    grab from desugaring a postprocessed version of the typechecked module, so we are
--    really independent from the \"normal\" compilation pipeline.
--
typecheckHook  :: Config -> TcGblEnv -> TcM (Either LiquidCheckException TcGblEnv)
typecheckHook cfg0 tcGblEnv = swapBreadcrumb thisModule Nothing >>= \case
  Just (Parsed parsed0) ->
    typecheckHook' cfg0 parsed0 tcGblEnv
  Nothing ->
    -- The module has been verified by an earlier call to the plugin.
    -- This could happen if multiple @-fplugin=LiquidHaskell@ flags are passed to GHC.
    -- See 'Breadcrumb' for more information.
    pure $ Right tcGblEnv
  where
    thisModule = tcg_mod tcGblEnv


typecheckHook' :: Config -> ParsedModule -> TcGblEnv -> TcM (Either LiquidCheckException TcGblEnv)
typecheckHook' cfg parsed tcGblEnv = do
  debugLog $ "We are in module: " <> show (toStableModule thisModule)

  case parseSpecComments (coerce specComments) of
    Left errors ->
      LH.filterReportErrors thisFile GHC.failM continue (getFilters cfg) Full errors
    Right specs ->
      liquidCheckModule cfg ms tcGblEnv specs

  where
    ms = pm_mod_summary parsed

    thisModule = ms_mod ms
    thisFile = LH.modSummaryHsFile ms

    specComments = map mkSpecComment $ LH.extractSpecComments parsed

    continue = pure $ Left (ErrorsOccurred [])

liquidCheckModule :: Config -> ModSummary -> TcGblEnv -> [BPspec] -> TcM (Either LiquidCheckException TcGblEnv)
liquidCheckModule cfg0 ms tcg specs = do
  updTopEnv (hscUpdateFlags noWarnings) $ do
    withPragmas cfg0 thisFile [s | Pragma s <- specs] $ \cfg -> do
        env <- getTopEnv

        pipelineData <- liftIO $ do
            session <- Session <$> newIORef env
            flip reflectGhc session $ mkPipelineData cfg ms tcg specs

        liquidLib <- liquidHaskellCheckWithConfig cfg pipelineData ms
        traverse (serialiseSpec thisModule tcg) liquidLib
  where
    thisModule = ms_mod ms
    thisFile = LH.modSummaryHsFile ms

    noWarnings dflags = dflags { warningFlags = mempty }

updateModSummaryDynFlags :: (DynFlags -> DynFlags) -> ModSummary -> ModSummary
updateModSummaryDynFlags f ms = ms { ms_hspp_opts = f (ms_hspp_opts ms) }

mkPipelineData :: (GhcMonad m) => Config -> ModSummary -> TcGblEnv -> [BPspec] -> m PipelineData
mkPipelineData cfg ms0 tcg0 specs = do
    let tcg = addNoInlinePragmasToBinds tcg0

    unoptimisedGuts <- withSession $ \hsc_env ->
        let lcl_hsc_env = hscSetFlags (ms_hspp_opts ms) hsc_env in
        liftIO $ hscDesugar lcl_hsc_env ms tcg

    resolvedNames   <- LH.lookupTyThings tcg
    avails          <- LH.availableTyThings tcg (tcg_exports tcg)
    let availTyCons = [ tc | ATyCon tc <- avails ]
        availVars   = [ var | AnId var <- avails ]

    let tcData = mkTcData (tcg_rn_imports tcg) resolvedNames availTyCons availVars
    return $ PipelineData unoptimisedGuts tcData specs
  where
    ms = updateModSummaryDynFlags (maybeInsertBreakPoints cfg . unoptimiseDynFlags) ms0

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

processInputSpec :: Config -> PipelineData -> ModSummary -> BareSpec -> TcM (Either LiquidCheckException LiquidLib)
processInputSpec cfg pipelineData modSummary inputSpec = do
  hscEnv <- env_top <$> getEnv
  debugLog $ " Input spec: \n" ++ show inputSpec
  debugLog $ "Relevant ===> \n" ++ unlines (renderModule <$> S.toList (relevantModules (hsc_mod_graph hscEnv) modGuts))

  logicMap :: LogicMap <- liftIO LH.makeLogicMap

  -- debugLog $ "Logic map:\n" ++ show logicMap

  let lhContext = LiquidHaskellContext {
        lhGlobalCfg       = cfg
      , lhInputSpec       = inputSpec
      , lhModuleLogicMap  = logicMap
      , lhModuleSummary   = modSummary
      , lhModuleTcData    = pdTcData pipelineData
      , lhModuleGuts      = pdUnoptimisedCore pipelineData
      , lhRelevantModules = relevantModules (hsc_mod_graph hscEnv) modGuts
      }

  -- liftIO $ putStrLn ("liquidHaskellCheck 6: " ++ show isIg)
  if isIgnore inputSpec
    then pure $ Left (ErrorsOccurred [])
    else checkLiquidHaskellContext lhContext

  where
    modGuts :: ModGuts
    modGuts = pdUnoptimisedCore pipelineData

liquidHaskellCheckWithConfig
  :: Config -> PipelineData -> ModSummary -> TcM (Either LiquidCheckException LiquidLib)
liquidHaskellCheckWithConfig cfg pipelineData modSummary = do
  -- Parse the spec comments stored in the pipeline data.
  let inputSpec = toBareSpec . snd $
        hsSpecificationP (moduleName thisModule) (pdSpecComments pipelineData)

  processInputSpec cfg pipelineData modSummary inputSpec
    `Ex.catch` (\(e :: UserError) -> reportErrs [e])
    `Ex.catch` (\(e :: Error) -> reportErrs [e])
    `Ex.catch` (\(es :: [Error]) -> reportErrs es)

  where
    thisFile = LH.modSummaryHsFile modSummary
    thisModule = ms_mod modSummary

    continue :: TcM (Either LiquidCheckException a)
    continue = pure $ Left (ErrorsOccurred [])

    reportErrs :: (Show e, F.PPrint e) => [TError e] -> TcM (Either LiquidCheckException a)
    reportErrs  = LH.filterReportErrors thisFile GHC.failM continue (getFilters cfg) Full

checkLiquidHaskellContext :: LiquidHaskellContext -> TcM (Either LiquidCheckException LiquidLib)
checkLiquidHaskellContext lhContext = do
  pmr <- processModule lhContext
  case pmr of
    Left e -> pure $ Left e
    Right ProcessModuleResult{..} -> do
      -- Call into the existing Liquid interface
      out <- liftIO $ LH.checkTargetInfo pmrTargetInfo

      let bareSpec = lhInputSpec lhContext
          file = LH.modSummaryHsFile $ lhModuleSummary lhContext

      withPragmas (lhGlobalCfg lhContext) file (Ms.pragmas $ fromBareSpec bareSpec) $ \moduleCfg ->  do
        let filters = getFilters moduleCfg
        -- Report the outcome of the checking
        LH.reportResult (errorLogger file filters) moduleCfg [giTarget (giSrc pmrTargetInfo)] out
        -- If there are unmatched filters or errors, and we are not reporting with
        -- json, we don't make it to this part of the code because errorLogger
        -- will throw an exception.
        --
        -- F.Crash is also handled by reportResult and errorLogger
        case o_result out of
          F.Safe _ -> return $ Right pmrClientLib
          _ | json moduleCfg -> failM
            | otherwise -> return $ Left $ ErrorsOccurred []

errorLogger :: FilePath -> [Filter] -> OutputResult -> TcM ()
errorLogger file filters outputResult = do
  LH.filterReportErrorsWith
    FilterReportErrorsArgs { errorReporter = \errs ->
                               LH.addTcRnUnknownMessages [(sp, e) | (sp, e) <- errs]
                           , filterReporter = LH.defaultFilterReporter file
                           , failure = GHC.failM
                           , continue = pure ()
                           , matchingFilters = LH.reduceFilters (\(src, doc) -> PJ.render doc ++ " at " ++ LH.showPpr src) filters
                           , filters = filters
                           }
    (LH.orMessages outputResult)

isIgnore :: BareSpec -> Bool
isIgnore (MkBareSpec sp) = any ((== "--skip-module") . F.val) (pragmas sp)

--------------------------------------------------------------------------------
-- | Working with bare & lifted specs ------------------------------------------
--------------------------------------------------------------------------------

loadDependencies :: Config -> [Module] -> TcM TargetDependencies
loadDependencies currentModuleConfig mods = do
  hscEnv    <- env_top <$> getEnv
  results   <- SpecFinder.findRelevantSpecs
                 (excludeAutomaticAssumptionsFor currentModuleConfig) hscEnv mods
  let deps = TargetDependencies $ foldl' processResult mempty (reverse results)
  redundant <- liftIO $ configToRedundantDependencies hscEnv currentModuleConfig

  debugLog $ "Redundant dependencies ==> " ++ show redundant

  pure $ foldl' (flip dropDependency) deps redundant
  where
    processResult
      :: HM.HashMap StableModule LiftedSpec
      -> SpecFinderResult
      -> HM.HashMap StableModule LiftedSpec
    processResult acc (SpecNotFound _mdl) = acc
    processResult acc (LibFound originalModule _location lib) =
      HM.insert
        (toStableModule originalModule)
        (libTarget lib)
        (acc <> getDependencies (libDeps lib))

data LiquidHaskellContext = LiquidHaskellContext {
    lhGlobalCfg        :: Config
  , lhInputSpec        :: BareSpec
  , lhModuleLogicMap   :: LogicMap
  , lhModuleSummary    :: ModSummary
  , lhModuleTcData     :: TcData
  , lhModuleGuts       :: ModGuts
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

processModule :: LiquidHaskellContext -> TcM (Either LiquidCheckException ProcessModuleResult)
processModule LiquidHaskellContext{..} = do
  debugLog ("Module ==> " ++ renderModule thisModule)
  hscEnv              <- env_top <$> getEnv

  let bareSpec        = lhInputSpec
  -- /NOTE/: For the Plugin to work correctly, we shouldn't call 'canonicalizePath', because otherwise
  -- this won't trigger the \"external name resolution\" as part of 'Language.Haskell.Liquid.Bare.Resolve'
  -- (cfr. 'allowExtResolution').
  let file            = LH.modSummaryHsFile lhModuleSummary

  _                   <- liftIO $ LH.checkFilePragmas $ Ms.pragmas (fromBareSpec bareSpec)

  withPragmas lhGlobalCfg file (Ms.pragmas $ fromBareSpec bareSpec) $ \moduleCfg -> do
    dependencies <- loadDependencies moduleCfg (S.toList lhRelevantModules)

    debugLog $ "Found " <> show (HM.size $ getDependencies dependencies) <> " dependencies:"
    when debugLogs $
      forM_ (HM.keys . getDependencies $ dependencies) $ debugLog . moduleStableString . unStableModule

    debugLog $ "mg_exports => " ++ O.showSDocUnsafe (O.ppr $ mg_exports modGuts)
    debugLog $ "mg_tcs => " ++ O.showSDocUnsafe (O.ppr $ mg_tcs modGuts)

    dynFlags <- getDynFlags
    targetSrc  <- liftIO $ makeTargetSrc moduleCfg dynFlags file lhModuleTcData modGuts hscEnv
    logger <- getLogger

    -- See https://github.com/ucsd-progsys/liquidhaskell/issues/1711
    -- Due to the fact the internals can throw exceptions from pure code at any point, we need to
    -- call 'evaluate' to force any exception and catch it, if we can.


    result <-
      makeTargetSpec moduleCfg lhModuleLogicMap targetSrc bareSpec dependencies

    let continue = pure $ Left (ErrorsOccurred [])
        reportErrs :: (Show e, F.PPrint e) => [TError e] -> TcRn (Either LiquidCheckException ProcessModuleResult)
        reportErrs = LH.filterReportErrors file GHC.failM continue (getFilters moduleCfg) Full

    (case result of
      -- Print warnings and errors, aborting the compilation.
      Left diagnostics -> do
        liftIO $ mapM_ (printWarning logger)    (allWarnings diagnostics)
        reportErrs $ allErrors diagnostics
      Right (warnings, targetSpec, liftedSpec) -> do
        liftIO $ mapM_ (printWarning logger) warnings
        let targetInfo = TargetInfo targetSrc targetSpec

        debugLog $ "bareSpec ==> "   ++ show bareSpec
        debugLog $ "liftedSpec ==> " ++ show liftedSpec

        let clientLib  = mkLiquidLib liftedSpec & addLibDependencies dependencies

        let result' = ProcessModuleResult {
              pmrClientLib  = clientLib
            , pmrTargetInfo = targetInfo
            }

        pure $ Right result')
      `Ex.catch` (\(e :: UserError) -> reportErrs [e])
      `Ex.catch` (\(e :: Error) -> reportErrs [e])
      `Ex.catch` (\(es :: [Error]) -> reportErrs es)

  where
    modGuts    = lhModuleGuts
    thisModule = mg_module modGuts

makeTargetSrc :: Config
              -> DynFlags
              -> FilePath
              -> TcData
              -> ModGuts
              -> HscEnv
              -> IO TargetSrc
makeTargetSrc cfg dynFlags file tcData modGuts hscEnv = do
  let preNormCoreBinds = preNormalizeCore cfg modGuts
  when (dumpPreNormalizedCore cfg) $ do
    putStrLn "\n*************** Pre-normalized CoreBinds *****************\n"
    putStrLn $ unlines $ L.intersperse "" $ map (GHC.showPpr dynFlags) preNormCoreBinds
  coreBinds <- anormalize cfg hscEnv modGuts { mg_binds = preNormCoreBinds }

  -- The type constructors for a module are the (nubbed) union of the ones defined and
  -- the ones exported. This covers the case of \"wrapper modules\" that simply re-exports
  -- everything from the imported modules.
  let availTcs    = tcAvailableTyCons tcData
  let allTcs      = L.nub (mgi_tcs mgiModGuts ++ availTcs)

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
  debugLog $ "allImports => " ++ show (tcAllImports tcData)
  debugLog $ "qualImports => " ++ show (tcQualifiedImports tcData)
  return $ TargetSrc
    { giTarget    = file
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

preNormalizeCore :: Config -> ModGuts -> [CoreBind]
preNormalizeCore cfg modGuts = rewriteBinds cfg inl_cbs
  where
    inl_cbs  = inlineAux cfg (mg_module modGuts) (mg_binds modGuts)

getFamInstances :: ModGuts -> [FamInst]
getFamInstances guts = famInstEnvElts (mg_fam_inst_env guts)
