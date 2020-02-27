{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ViewPatterns               #-}

module Language.Haskell.Liquid.GHC.Plugin (

  -- * The Plugin
  plugin

  ) where

import qualified Outputable as O
import GHC hiding (Target, Located, desugarModule)

import Plugins as GHC
import TcRnTypes as GHC
import TcRnMonad as GHC
import GHC.ThToHs as GHC

import qualified Language.Haskell.Liquid.GHC.Misc as LH
import qualified Language.Haskell.Liquid.UX.CmdLine as LH
import qualified Language.Haskell.Liquid.UX.Config as LH
import qualified Language.Haskell.Liquid.GHC.Interface as LH
import qualified Language.Haskell.Liquid.Liquid as LH

import Language.Haskell.Liquid.GHC.Plugin.Types
import Language.Haskell.Liquid.GHC.Plugin.Util as Util
import Language.Haskell.Liquid.GHC.Plugin.SpecFinder as SpecFinder

import qualified Language.Haskell.Liquid.GHC.API as Ghc
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike
import Language.Haskell.Liquid.GHC.GhcMonadLike (GhcMonadLike, askHscEnv)
import CoreMonad
import DataCon
import DynFlags
import HscTypes hiding (Target)
import InstEnv
import Module
import Panic (throwGhcException)
import qualified TysPrim
import GHC.LanguageExtensions

import Control.Exception
import Control.Monad

import           Data.Function                            ( (&) )
import Data.Coerce
import Data.List as L hiding (intersperse)
import Data.IORef
import qualified Data.Set as S
import Data.Set (Set)


import qualified Data.HashSet        as HS
import           Data.HashSet                             ( HashSet )

import System.IO.Unsafe                 (unsafePerformIO)
import Text.Parsec.Pos
import Language.Fixpoint.Types          hiding (panic, Error, Result, Expr)

import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GHC.Misc
import qualified Language.Haskell.Liquid.Measure  as Ms
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Types hiding (Spec, getConfig)
import Language.Haskell.Liquid.UX.CmdLine

---------------------------------------------------------------------------------
-- | State and configuration management -----------------------------------------
---------------------------------------------------------------------------------

-- | A reference to cache the LH's 'Config' and produce it only /once/, during the dynFlags hook.
cfgRef :: IORef Config
cfgRef = unsafePerformIO $ newIORef defConfig
{-# NOINLINE cfgRef #-}

unoptimisedRef :: IORef (Unoptimised ModGuts)
unoptimisedRef = unsafePerformIO $ newIORef (error "Impossible, unoptimisedRef was un-initialised.")
{-# NOINLINE unoptimisedRef #-}

tcStableRef :: IORef (ModuleEnv TcData)
tcStableRef = unsafePerformIO $ newIORef emptyModuleEnv
{-# NOINLINE tcStableRef #-}

-- | Set to 'True' to enable debug logging.
debugLogs :: Bool
debugLogs = True

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
    parsedResultAction    = parseHook
  , typeCheckResultAction = typecheckHook
  , installCoreToDos      = coreHook
  , dynflagsPlugin        = customDynFlags
  , pluginRecompile       = \_ -> pure ForceRecompile
  , interfaceLoadAction   = loadInterfaceHook
  }

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

-- | Overrides the default 'DynFlags' options. Specifically, we need the GHC
-- lexer not to throw away block comments, as this is where the LH spec comments
-- would live. This is why we set the 'Opt_KeepRawTokenStream' option.
customDynFlags :: [CommandLineOption] -> DynFlags -> IO DynFlags
customDynFlags opts dflags = do
  debugLog "hello"
  cfg <- liftIO $ LH.getOpts opts
  writeIORef cfgRef cfg
  configureDynFlags dflags

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
-- | Parsing phase -------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Hook into the parsing phase and extract \"LiquidHaskell\"'s spec comments, turning them into
-- module declarations (i.e. 'LhsDecl GhcPs') which can be later be consumed in the typechecking phase.
-- The goal for this phase is /not/ to turn spec comments into a fully-fledged data structure, but rather
-- carry those string fragments (together with their 'SourcePos') into the next phase.
parseHook :: [CommandLineOption] 
          -> ModSummary 
          -> HsParsedModule 
          -> Hsc HsParsedModule
parseHook _ modSummary parsedModule = do
  -- NOTE: We need to reverse the order of the extracted spec comments because in the plugin infrastructure
  -- those would appear in reverse order and LiquidHaskell is sensible to the order in which these
  -- annotations appears.
  let comments  = L.reverse $ LH.extractSpecComments (hpm_annotations parsedModule)

  commentsExps <- mapM (liftIO . TH.runQ . TH.liftData . SpecComment) comments

  let module' = parsedModule { 
      hpm_module =
          fmap (specCommentsToModuleAnnotations (zip comments commentsExps)) 
               (hpm_module parsedModule) 
  }

  -- \"The ugly hack\": grab the unoptimised core binds here.
  parsed          <- GhcMonadLike.parseModule (unoptimise . LH.keepRawTokenStream $ modSummary)

  -- Calling 'typecheckModule' here will load some interfaces which won't be re-opened by the
  -- 'loadInterfaceAction'. Therefore it's necessary we do all the lookups for necessary specs elsewhere.
  typechecked     <- GhcMonadLike.typecheckModule (LH.ignoreInline parsed)
  unoptimisedGuts <- GhcMonadLike.desugarModule typechecked

  liftIO $ writeIORef unoptimisedRef (toUnoptimised unoptimisedGuts)

  debugLog $ (O.showSDocUnsafe $ O.ppr (mg_binds unoptimisedGuts))

  -- Resolve names and imports
  env <- askHscEnv
  resolvedNames <- LH.lookupTyThings env (GhcMonadLike.tm_mod_summary typechecked) 
                                         (GhcMonadLike.tm_gbl_env typechecked)

  let thisModule = ms_mod modSummary
  let stableData = mkTcData typechecked resolvedNames

  -- Extend the 'ModuleEnv' held by the 'tcStableRef' with the data from this module.
  liftIO $ atomicModifyIORef' tcStableRef (\old -> (extendModuleEnv old thisModule stableData, ()))

  pure module'

  where
    specCommentsToModuleAnnotations :: [((SourcePos, String), TH.Exp)] -> HsModule GhcPs -> HsModule GhcPs
    specCommentsToModuleAnnotations comments m = 
      m { hsmodDecls = map toAnnotation comments ++ hsmodDecls m }
      where
        toAnnotation :: ((SourcePos, String), TH.Exp) -> LHsDecl GhcPs
        toAnnotation ((pos, _specContent), thExpr) = 
            let located = GHC.L (LH.sourcePosSrcSpan pos)
                hsExpr = either (throwGhcException . ProgramError 
                                                   . mappend "specCommentsToModuleAnnotations failed : " 
                                                   . O.showSDocUnsafe) id $ 
                           convertToHsExpr Ghc.Generated (LH.sourcePosSrcSpan pos) thExpr
                annDecl = HsAnnotation @GhcPs noExtField Ghc.NoSourceText ModuleAnnProvenance hsExpr
            in located $ AnnD noExtField annDecl


--------------------------------------------------------------------------------
-- | \"Unoptimising\" things ----------------------------------------------------
--------------------------------------------------------------------------------

-- | LiquidHaskell requires the unoptimised core binds in order to work correctly, but at the same time the
-- user can invoke GHC with /any/ optimisation flag turned out. This is why we grab the core binds by
-- desugaring the module during /parsing/ (before that's already too late) and we cache the core binds for
-- the rest of the program execution.
class Unoptimise a where
  type UnoptimisedTarget a :: *
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
-- | Core phase ----------------------------------------------------------------
--------------------------------------------------------------------------------

coreHook :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
coreHook _ passes = do
  cfg <- liftIO getConfig
  pure (CoreDoPluginPass "Language.Haskell.Liquid.GHC.Plugin" (liquidHaskellPass cfg) : passes)

-- | Partially calls into LiquidHaskell's GHC API.
liquidHaskellPass :: LH.Config -> ModGuts -> CoreM ModGuts
liquidHaskellPass cfg modGuts = do

  let thisModule = mg_module modGuts

  -- Immediately check if this is a LH-annotated module. If not, skip it altogether.
  -- Generate the bare-specs. Here we call 'extractSpecComments' which is what allows us to
  -- retrieve the 'SpecComment' information we computed in the 'parseHook' phase.
  let (guts', specComments) = Util.extractSpecComments modGuts
  let specQuotes = LH.extractSpecQuotes' mg_module mg_anns modGuts
  bareSpec <- getLiquidSpec thisModule specComments specQuotes

  case needsProcessing bareSpec of
    False -> pure guts'
    True  -> do
      modSummary <- GhcMonadLike.getModSummary (moduleName thisModule)
      dynFlags <- getDynFlags
      mbTcData <- (`lookupModuleEnv` thisModule) <$> liftIO (readIORef tcStableRef)
      unoptimisedGuts <- liftIO $ readIORef unoptimisedRef

      case mbTcData of
        Nothing -> Util.pluginAbort dynFlags (O.text "No tcData found for " O.<+> O.ppr thisModule)
        Just tcData -> do

          debugLog $ "Relevant ===> \n" ++ 
            (unlines $ map debugShowModule $ (S.toList $ relevantModules modGuts))

          logicMap <- liftIO $ LH.makeLogicMap

          let lhContext = LiquidHaskellContext {
                lhGlobalCfg       = cfg
              , lhBareSpec        = bareSpec
              , lhModuleLogicMap  = logicMap
              , lhModuleSummary   = modSummary
              , lhModuleTcData    = tcData
              , lhModuleGuts      = unoptimisedGuts
              , lhRelevantModules = relevantModules modGuts
              }

          ProcessModuleResult{..} <- processModule lhContext

          let finalGuts = Util.serialiseLiquidLib pmrClientLib guts'

          -- Call into the existing Liquid interface
          res <- liftIO $ LH.liquidOne pmrGhcInfo
          case o_result res of
            Safe -> pure ()
            _    -> pluginAbort dynFlags (O.text "Unsafe.")

          debugLog $ "Serialised annotations ==> " ++ (O.showSDocUnsafe . O.vcat . map O.ppr . mg_anns $ finalGuts)
          pure finalGuts

--------------------------------------------------------------------------------
-- | Working with bare & lifted specs ------------------------------------------
--------------------------------------------------------------------------------

loadRelevantSpecs :: forall m. GhcMonadLike m 
                  => (Config, Bool)
                  -> ExternalPackageState
                  -> HomePackageTable
                  -> Module
                  -> [Module]
                  -> m (HashSet CachedSpec)
loadRelevantSpecs config eps hpt thisModule mods = do
  results <- SpecFinder.findRelevantSpecs config eps hpt mods
  foldlM processResult mempty (reverse results)
  where
    processResult :: HashSet CachedSpec -> SpecFinderResult -> m (HashSet CachedSpec)
    processResult !acc (SpecNotFound mdl) = do
      debugLog $ "[T:" ++ debugShowModule thisModule
              ++ "] Spec not found for " ++ debugShowModule mdl
      pure acc
    processResult !acc (SpecFound originalModule location lib) = do
      debugLog $ "[T:" ++ show (moduleName thisModule) 
              ++ "] Spec found for " ++ debugShowModule originalModule ++ ", at location " ++ show location
      pure $ toCached originalModule (libTarget lib) `HS.insert` acc <> libDeps lib


-- | The collection of dependencies and usages modules which are relevant for liquidHaskell
relevantModules :: ModGuts -> Set Module
relevantModules modGuts = used `S.union` dependencies
  where
    dependencies :: Set Module
    dependencies = S.fromList $ map (toModule . fst) . filter (not . snd) . dep_mods $ deps

    deps :: Dependencies
    deps = mg_deps modGuts

    thisModule :: Module
    thisModule = mg_module modGuts

    toModule :: ModuleName -> Module
    toModule = Module (moduleUnitId thisModule)

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
  , lhBareSpec         :: BareSpec
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
  , pmrGhcInfo    :: GhcInfo
  -- ^ The 'GhcInfo' for the current 'Module' that LiquidHaskell will process.
  }

-- | Returns 'True' if we have to process the 'Module' associated to the input 'BareSpec'.
needsProcessing :: BareSpec -> Bool
needsProcessing = not . nullSpec

getLiquidSpec :: GhcMonadLike m => Module -> [SpecComment] -> [BPspec] -> m BareSpec
getLiquidSpec thisModule specComments specQuotes = do

  (_, commSpec) <- either throw return $ 
    hsSpecificationP (moduleName thisModule) (coerce specComments) specQuotes

  res <- SpecFinder.findCompanionSpec thisModule
  case res of
    SpecFound _ _ lib -> do
      debugLog $ "Companion spec found for " ++ debugShowModule thisModule
      pure $ commSpec `mergeSpecs` libTarget lib
    _ -> pure commSpec

processModule :: GhcMonadLike m => LiquidHaskellContext -> m ProcessModuleResult
processModule LiquidHaskellContext{..} = do
  debugLog ("Module ==> " ++ debugShowModule thisModule)
  hscEnv              <- askHscEnv

  let bareSpec        = lhBareSpec
  -- /NOTE/: For the Plugin to work correctly, we shouldn't call 'canonicalizePath', because otherwise
  -- this won't trigger the \"external name resolution\" as part of 'Language.Haskell.Liquid.Bare.Resolve'
  -- (cfr. 'allowExtResolution').
  let file            = LH.modSummaryHsFile lhModuleSummary

  _                   <- LH.checkFilePragmas $ Ms.pragmas bareSpec

  moduleCfg           <- liftIO $ withPragmas lhGlobalCfg file (Ms.pragmas bareSpec)
  eps                 <- liftIO $ readIORef (hsc_EPS hscEnv)

  let configChanged   = moduleCfg /= lhGlobalCfg
  dependencies       <- loadRelevantSpecs (moduleCfg, configChanged)
                                          eps
                                          (hsc_HPT hscEnv)
                                          thisModule
                                          (S.toList lhRelevantModules)

  debugLog $ "Found " <> show (length dependencies) <> " dependencies:"
  forM_ dependencies $ debugLog . cachedSpecStableModuleId


  ghcSrc              <- makeGhcSrc moduleCfg file lhModuleTcData modGuts hscEnv
  let bareSpecs        = makeBareSpecs (moduleName thisModule) bareSpec dependencies

  let ghcSpec          = makeGhcSpec moduleCfg ghcSrc lhModuleLogicMap bareSpecs
  let ghcInfo          = GI ghcSrc ghcSpec

  -- /NOTE/: Grab the spec out of the validated 'GhcSpec', which will be richer than the original one.
  -- This is the one we want to cache and serialise into the annotations, otherwise we would get validation
  -- errors when trying to refine things.
  let clientSpec = (gsLSpec . giSpec $ ghcInfo) `mergeSpecs` bareSpec
  let clientLib  = mkLiquidLib clientSpec & addLibDependencies dependencies


  let result = ProcessModuleResult {
        pmrClientLib  = clientLib
      , pmrGhcInfo    = ghcInfo
      }

  pure result

  where
    modGuts    = fromUnoptimised lhModuleGuts
    thisModule = mg_module modGuts

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen 
---------------------------------------------------------------------------------------

makeGhcSrc :: GhcMonadLike m
           => Config
           -> FilePath 
           -> TcData
           -> ModGuts
           -> HscEnv
           -> m GhcSrc
makeGhcSrc cfg file tcData modGuts hscEnv = do
  coreBinds      <- liftIO $ anormalize cfg hscEnv modGuts
  let dataCons    = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs mgiModGuts)
  (fiTcs, fiDcs) <- liftIO $ LH.makeFamInstEnv hscEnv
  let things      = tcResolvedNames tcData
  let impVars     = LH.importVars coreBinds ++ LH.classCons (mgi_cls_inst mgiModGuts)
  return $ Src
    { giIncDir    = mempty
    , giTarget    = file
    , giTargetMod = ModName Target (moduleName (mg_module modGuts))
    , giCbs       = coreBinds
    , giImpVars   = impVars
    , giDefVars   = dataCons ++ (letVars coreBinds)
    , giUseVars   = readVars coreBinds
    , giDerVars   = HS.fromList (LH.derivedVars cfg mgiModGuts)
    , gsExports   = mgi_exports  mgiModGuts
    , gsTcs       = mgi_tcs      mgiModGuts
    , gsCls       = mgi_cls_inst mgiModGuts
    , gsFiTcs     = fiTcs
    , gsFiDcs     = fiDcs
    , gsPrimTcs   = TysPrim.primTyCons
    , gsQualImps  = tcQualifiedImports tcData
    , gsAllImps   = tcAllImports       tcData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }
  where
    mgiModGuts :: MGIModGuts
    mgiModGuts = miModGuts deriv modGuts
      where
        deriv   = Just $ instEnvElts $ mg_inst_env modGuts

---------------------------------------------------------------------------------------
-- | @makeBareSpecs@ loads BareSpec for target and imported modules 
---------------------------------------------------------------------------------------
makeBareSpecs :: ModuleName -> Ms.BareSpec -> HashSet CachedSpec -> [(ModName, BareSpec)]
makeBareSpecs mname tgtSpec dependencies = 
  let tgtMod    = ModName Target mname
  in  (tgtMod, tgtSpec) : map fromCached (HS.toList dependencies)

---------------------------------------------------------------------------------
-- | Unused stages of the compilation pipeline ----------------------------------
---------------------------------------------------------------------------------

typecheckHook :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
typecheckHook _ _ tcGblEnv =  pure tcGblEnv

loadInterfaceHook :: [CommandLineOption] -> ModIface -> IfM lcl ModIface
loadInterfaceHook _ iface = pure iface
