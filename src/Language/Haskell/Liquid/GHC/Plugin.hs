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
import qualified GHC
import GHC.Paths (libdir)
import GHC.Serialized

import qualified Data.Binary as B
import qualified Data.ByteString.Lazy as B

import Plugins as GHC
import Annotations as GHC
import GHC.Hs as GHC
import TcRnTypes as GHC
import TcRnMonad as GHC
import TcRnDriver as GHC
import Finder as GHC
import GHC.ThToHs as GHC
import HscMain (hscGetModuleInterface)

import qualified Language.Haskell.Liquid.GHC.Misc as LH
import qualified Language.Haskell.Liquid.Parse as LH
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
import Annotations
import Class
import CoreMonad
import CoreSyn
import DataCon
import Digraph
import DriverPhases
import DriverPipeline
import DynFlags
import Finder
import HscTypes hiding (Target)
import IdInfo
import InstEnv
import Module
import Panic (throwGhcExceptionIO, throwGhcException)
import TcRnTypes
import Var
import FastString
import FamInstEnv
import FamInst
import qualified TysPrim
import GHC.LanguageExtensions
import UniqFM

import Control.Exception
import Control.Monad
import Control.Applicative ((<|>))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe

import Data.Bifunctor
import Data.Coerce
import Data.Data
import Data.List as L hiding (intersperse)
import Data.Maybe
import Data.IORef
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Set (Set)

import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import qualified Data.HashSet        as HS

import System.Console.CmdArgs.Verbosity hiding (Loud)
import System.Directory
import System.FilePath
import System.IO.Temp
import System.IO.Unsafe                 (unsafePerformIO)
import Text.Parsec.Pos
import Text.PrettyPrint.HughesPJ        hiding (first, (<>))
import Language.Fixpoint.Types          hiding (panic, Error, Result, Expr)
import qualified Language.Fixpoint.Misc as Misc

import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.GHC.Play
import Language.Haskell.Liquid.WiredIn (isDerivedInstance) 
import qualified Language.Haskell.Liquid.Measure  as Ms
import qualified Language.Haskell.Liquid.Misc     as Misc
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Types hiding (Spec, getConfig)
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.UX.Config (totalityCheck)
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.UX.Tidy
import Language.Fixpoint.Utils.Files

import Debug.Trace

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

-- Used to carry around all the specs we discover while processing interface files and their
-- annotations.
ifaceStableRef :: IORef SpecEnv
ifaceStableRef = unsafePerformIO $ newIORef mempty
{-# NOINLINE ifaceStableRef #-}

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

-- | Overrides the default 'DynFlags' options. Specifically, we need the GHC
-- lexer not to throw away block comments, as this is where the LH spec comments
-- would live. This is why we set the 'Opt_KeepRawTokenStream' option.
customDynFlags :: [CommandLineOption] -> DynFlags -> IO DynFlags
customDynFlags opts dflags = do
  cfg <- liftIO $ LH.getOpts opts
  writeIORef cfgRef cfg
  {- updOptLevel 0 <$> -} 
  configureDynFlags cfg dflags

--
-- Parsing phase
--

-- | Hook into the parsing phase and extract \"LiquidHaskell\"'s spec comments, turning them into
-- module declarations (i.e. 'LhsDecl GhcPs') which can be later be consumed in the typechecking phase.
-- The goal for this phase is /not/ to turn spec comments into a fully-fledged data structure, but rather
-- carry those string fragments (together with their 'SourcePos') into the next phase.
parseHook :: [CommandLineOption] 
          -> ModSummary 
          -> HsParsedModule 
          -> Hsc HsParsedModule
parseHook opts modSummary parsedModule = do
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
  parsedModule    <- GhcMonadLike.parseModule (unoptimise . LH.keepRawTokenStream $ modSummary)

  -- Calling 'typecheckModule' here will load some interfaces which won't be re-opened by the
  -- 'loadInterfaceAction'. Therefore it's necessary we do all the lookups for necessary specs elsewhere.
  typechecked     <- GhcMonadLike.typecheckModule (LH.ignoreInline parsedModule)
  unoptimisedGuts <- GhcMonadLike.desugarModule typechecked

  liftIO $ writeIORef unoptimisedRef (toUnoptimised unoptimisedGuts)

  debugLog $ (O.showSDocUnsafe $ O.ppr (mg_binds unoptimisedGuts))

  pure module'

  where

    specCommentsToModuleAnnotations :: [((SourcePos, String), TH.Exp)] 
                                    -> HsModule GhcPs 
                                    -> HsModule GhcPs
    specCommentsToModuleAnnotations comments m = 
      m { hsmodDecls = map toAnnotation comments ++ hsmodDecls m }
      where
        toAnnotation :: ((SourcePos, String), TH.Exp) -> LHsDecl GhcPs
        toAnnotation ((pos, specContent), expr) = 
            let located = GHC.L (LH.sourcePosSrcSpan pos)
                hsExpr = either (throwGhcException . ProgramError 
                                                   . mappend "specCommentsToModuleAnnotations failed : " 
                                                   . O.showSDocUnsafe) id $ 
                           convertToHsExpr Ghc.Generated (LH.sourcePosSrcSpan pos) expr
                annDecl = HsAnnotation @GhcPs noExtField Ghc.NoSourceText ModuleAnnProvenance hsExpr
            in located $ AnnD noExtField annDecl


--
-- \"Unoptimising\" things.
--

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


--
-- Typechecking phase
--

-- | Currently we don't do anything in this phase.
typecheckHook :: [CommandLineOption] 
              -> ModSummary 
              -> TcGblEnv 
              -> TcM TcGblEnv
typecheckHook opts modSummary tcGblEnv = do
  env <- askHscEnv
  resolvedNames <- resolveNames env modSummary tcGblEnv

  let thisModule = ms_mod modSummary
  let stableData = mkTcData tcGblEnv resolvedNames

  -- Extend the 'ModuleEnv' held by the 'tcStableRef' with the data from this module.
  liftIO $ atomicModifyIORef' tcStableRef (\old -> (extendModuleEnv old thisModule stableData, ()))

  pure tcGblEnv

--
-- Core phase
--

coreHook :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
coreHook opts passes = do
  cfg <- liftIO getConfig
  pure (CoreDoPluginPass "Language.Haskell.Liquid.GHC.Plugin" (liquidHaskellPass cfg) : passes)

-- | Partially calls into LiquidHaskell's GHC API.
liquidHaskellPass :: LH.Config -> ModGuts -> CoreM ModGuts
liquidHaskellPass cfg modGuts = do
  let thisModule = mg_module modGuts
  dynFlags <- getDynFlags
  modSummary <- GhcMonadLike.getModSummary (moduleName thisModule)
  mbTcData <- (`lookupModuleEnv` thisModule) <$> liftIO (readIORef tcStableRef)
  unoptimisedGuts <- liftIO $ readIORef unoptimisedRef

  debugLog $ "liquidHaskellPass => " ++ (O.showSDocUnsafe $ O.ppr (mg_binds modGuts))

  case mbTcData of
    Nothing -> Util.pluginAbort dynFlags (O.text "No tcData found for " O.<+> O.ppr thisModule)
    Just tcData -> do
      specEnv  <- liftIO $ readIORef ifaceStableRef

      debugLog $ "Relevant ===> \n" ++ (O.showSDocUnsafe . O.vcat . map O.ppr $ (S.toList $ relevantModules modGuts))

      -- Generate the bare-specs. Here we call 'extractSpecComments' which is what allows us to
      -- retrieve the 'SpecComment' information we computed in the 'parseHook' phase.
      let (guts', specComments) = Util.extractSpecComments modGuts
      let specQuotes = LH.extractSpecQuotes' mg_module mg_anns modGuts

      logicMap <- liftIO $ LH.makeLogicMap

      let lhContext = LiquidHaskellContext {
            lhModuleCfg       = cfg
          , lhModuleLogicMap  = logicMap
          , lhModuleSummary   = modSummary
          , lhModuleTcData    = tcData
          , lhModuleGuts      = unoptimisedGuts
          , lhRelevantModules = relevantModules modGuts
          , lhSpecEnv         = specEnv
          , lhSpecComments    = specComments
          , lhSpecQuotes      = specQuotes
          }

      -- Call into the interface
      thisFile <- liftIO $ canonicalizePath $ LH.modSummaryHsFile modSummary

      (bareSpec, newSpecEnv, ghcInfo) <- processModule lhContext

      -- Persist the 'BareSpec' in the final interface file by adding it as a new 'Annotation' to the 'ModGuts'.
      let finalGuts = Util.serialiseBareSpecs [bareSpec] guts'

      res <- liftIO $ LH.liquidOne ghcInfo
      case o_result res of
        Safe -> pure ()
        _    -> pluginAbort dynFlags (O.text "Unsafe.")

      liftIO $ atomicModifyIORef' ifaceStableRef (\old -> (newSpecEnv, ()))

      debugLog $ "Serialised annotations ==> " ++ (O.showSDocUnsafe . O.vcat . map O.ppr . mg_anns $ finalGuts)
      pure finalGuts

loadRelevantSpecs :: forall m. GhcMonadLike m 
                  => Config 
                  -> ExternalPackageState
                  -> SpecEnv 
                  -> TargetModule
                  -> [Module]
                  -> m SpecEnv
loadRelevantSpecs config eps specEnv targetModule mods = do
  (newSpec, results) <- SpecFinder.findRelevantSpecs config eps specEnv targetModule mods
  mapM_ processResult results
  pure newSpec
  where
    processResult :: SpecFinderResult -> m ()
    processResult (SpecNotFound modName) = do
      debugLog $ "[T:" ++ show (moduleName $ getTargetModule targetModule) 
              ++ "] Spec not found for " ++ show modName
    processResult (SpecFound location (fromCached -> spec)) = do
      debugLog $ "[T:" ++ show (moduleName $ getTargetModule targetModule) 
              ++ "] Spec found for " ++ show (fst spec) ++ ", at location " ++ show location
    processResult (MultipleSpecsFound location (map fromCached . HS.toList -> specs)) = do
      debugLog $ "[T:" ++ show (moduleName $ getTargetModule targetModule) 
              ++ "] Multiple specs found : " 
      debugLog $ unlines (map (show . fst) specs)
               ++ "\nAt location " ++ show location

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
    lhModuleCfg        :: Config
  , lhModuleLogicMap   :: LogicMap
  , lhModuleSummary    :: ModSummary
  , lhModuleTcData     :: TcData
  , lhModuleGuts       :: Unoptimised ModGuts
  , lhRelevantModules  :: Set Module
  , lhSpecEnv          :: SpecEnv
  , lhSpecComments     :: [SpecComment]
  , lhSpecQuotes       :: [BPspec]
  }

--
-- Interface phase
--
-- This allows us to modify an interface that have been loaded. This is crucial to find
-- specs which has been already extracted and processed, because the plugin architecture will
-- call this for dependencies /before/ entering the /Core/ pipeline for the module being compiled.
--

loadInterfaceHook :: [CommandLineOption] -> ModIface -> IfM lcl ModIface
loadInterfaceHook opts iface = do
    debugLog $ "loadInterfaceHook for " ++ (show . moduleName . mi_module $ iface)
    pure iface

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

updateIncludePaths :: DynFlags -> [FilePath] -> IncludeSpecs 
updateIncludePaths df ps = addGlobalInclude (includePaths df) ps 

configureDynFlags :: Config -> DynFlags -> IO DynFlags
configureDynFlags cfg df =
  pure $ df { importPaths  = nub $ idirs cfg ++ importPaths df
            , libraryPaths = nub $ idirs cfg ++ libraryPaths df
            , includePaths = updateIncludePaths df (idirs cfg)
            } `gopt_set` Opt_ImplicitImportQualified
              `gopt_set` Opt_PIC
              `gopt_set` Opt_DeferTypedHoles
              `gopt_set` Opt_KeepRawTokenStream
              `xopt_set` MagicHash
              `xopt_set` DeriveGeneric
              `xopt_set` StandaloneDeriving

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

processModule :: GhcMonadLike m => LiquidHaskellContext -> m (Ms.BareSpec, SpecEnv, GhcInfo)
processModule LiquidHaskellContext{..} = do
  debugLog ("Module ==> " ++ show (moduleName thisModule))
  hscEnv              <- askHscEnv
  file                <- liftIO $ canonicalizePath $ LH.modSummaryHsFile lhModuleSummary
  (modName, bareSpec) <- either throw return $ 
    hsSpecificationP (moduleName thisModule) (coerce lhSpecComments) lhSpecQuotes
  _                   <- LH.checkFilePragmas $ Ms.pragmas bareSpec
  let termlessSpec     = LH.noTerm bareSpec

  cfg                 <- liftIO $ withPragmas lhModuleCfg file (Ms.pragmas bareSpec)
  eps                 <- liftIO $ readIORef (hsc_EPS hscEnv)

  updatedEnv          <-
    loadRelevantSpecs cfg eps lhSpecEnv (SpecFinder.TargetModule thisModule) (S.toList lhRelevantModules)

  ghcSrc              <- makeGhcSrc cfg file lhModuleTcData modGuts hscEnv
  bareSpecs           <- makeBareSpecs cfg updatedEnv (moduleName thisModule) bareSpec
  let ghcSpec          = makeGhcSpec   cfg ghcSrc lhModuleLogicMap (map fromCached . HS.toList $ bareSpecs)
  let ghcInfo          = GI ghcSrc ghcSpec
  let finalEnv         = M.insert thisModule (HS.singleton $ toCached (modName, termlessSpec)) updatedEnv

  pure (termlessSpec, finalEnv, ghcInfo)

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
  df <- unoptimise <$> getDynFlags
  let mgiModGuts    = makeMGIModGuts modGuts
  ms <- GhcMonadLike.getModSummary (moduleName $ mg_module $ modGuts)
  coreBinds         <- liftIO $ anormalize cfg (unoptimise (df, hscEnv)) modGuts
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs mgiModGuts)
  (fiTcs, fiDcs)    <- liftIO $ LH.makeFamInstEnv hscEnv
  let things        = tcResolvedNames tcData
  let impVars        = LH.importVars coreBinds ++ LH.classCons (mgi_cls_inst mgiModGuts)
  incDir            <- liftIO $ Misc.getIncludeDir
  return $ Src
    { giIncDir    = incDir
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
    , gsQualImps  = qualifiedImports tcData
    , gsAllImps   = allImports       tcData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }
  where
    makeMGIModGuts :: ModGuts -> MGIModGuts
    makeMGIModGuts modGuts = miModGuts deriv modGuts
      where
        deriv   = Just $ instEnvElts $ mg_inst_env modGuts

allImports :: TcData -> HS.HashSet Symbol 
allImports tcData = HS.fromList (symbol . unLoc . ideclName . unLoc <$> tcImports tcData)

qualifiedImports :: TcData -> QImports 
qualifiedImports (tcImports -> imps) =
  LH.qImports [ (qn, n) | i         <- imps
                        , let decl   = unLoc i
                        , let m      = unLoc (ideclName decl)  
                        , qm        <- maybeToList (unLoc <$> ideclAs decl) 
                        , let [n,qn] = symbol <$> [m, qm] 
                        ]

---------------------------------------------------------------------------------------
-- | @lookupTyThings@ grabs all the @Name@s and associated @TyThing@ known to GHC 
--   for this module; we will use this to create our name-resolution environment 
--   (see `Bare.Resolve`)                                          
---------------------------------------------------------------------------------------
lookupTyThings :: GhcMonadLike m 
               => HscEnv 
               -> GhcMonadLike.ModuleInfo 
               -> MGIModGuts 
               -> m [(Name, Maybe TyThing)] 
lookupTyThings hscEnv mi mg = do
  forM (mgNames mg) $ \n -> do 
    tt1 <-          GhcMonadLike.lookupName      n
    tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n
    tt3 <-          GhcMonadLike.modInfoLookupName mi n
    tt4 <-          GhcMonadLike.lookupGlobalName n 
    return (n, Misc.firstMaybes [tt1, tt2, tt3, tt4])
  where
    mgNames :: MGIModGuts -> [Ghc.Name] 
    mgNames  = fmap Ghc.gre_name . Ghc.globalRdrEnvElts .  mgi_rdr_env 

resolveNames :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> m [(Name, Maybe TyThing)]
resolveNames hscEnv modSum tcGblEnv = do
  mi <- GhcMonadLike.moduleInfoTc modSum tcGblEnv
  forM names $ \n -> do 
    tt1 <-          GhcMonadLike.lookupName      n
    tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n
    tt3 <-          GhcMonadLike.modInfoLookupName mi n
    tt4 <-          GhcMonadLike.lookupGlobalName n 
    return (n, Misc.firstMaybes [tt1, tt2, tt3, tt4])
  where
    names :: [Ghc.Name] 
    names  = fmap Ghc.gre_name . Ghc.globalRdrEnvElts $ tcg_rdr_env tcGblEnv

---------------------------------------------------------------------------------------
-- | @makeBareSpecs@ loads BareSpec for target and imported modules 
---------------------------------------------------------------------------------------
makeBareSpecs :: GhcMonadLike m
              => Config 
              -> SpecEnv 
              -> ModuleName
              -> Ms.BareSpec 
              -> m (HS.HashSet CachedSpec)
makeBareSpecs cfg specEnv thisModule tgtSpec = do 
  let allSpecs    = M.elems specEnv
  let tgtMod      = ModName Target thisModule
  return          $ CachedSpec tgtMod (WrappedSpec tgtSpec) `HS.insert` (mconcat allSpecs)

