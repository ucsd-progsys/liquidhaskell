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

import Prelude hiding (error)

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

import Language.Haskell.Liquid.GHC.Plugin.Types (SpecComment(..), TcStableData, mkTcStableData, tcStableImports)
import Language.Haskell.Liquid.GHC.Plugin.Util as Util

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

import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import qualified Data.HashSet        as S
import qualified Data.Map            as M

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

import qualified Debug.Trace as Debug 

-- | A reference to cache the LH's 'Config' and produce it only /once/, during the dynFlags hook.
cfgRef :: IORef Config
cfgRef = unsafePerformIO $ newIORef defConfig
{-# NOINLINE cfgRef #-}

tcStableRef :: IORef (ModuleEnv TcStableData)
tcStableRef = unsafePerformIO $ newIORef emptyModuleEnv
{-# NOINLINE tcStableRef #-}

-- Used to carry around all the specs we discover while processing interface files and their
-- annotations.
ifaceStableRef :: IORef SpecEnv
ifaceStableRef = unsafePerformIO $ newIORef emptyModuleEnv
{-# NOINLINE ifaceStableRef #-}

testRef :: IORef Int
testRef = unsafePerformIO $ newIORef 0
{-# NOINLINE testRef #-}

-- | Reads the 'Config' out of a 'IORef'.
getConfig :: IO Config
getConfig = readIORef cfgRef

--------------------------------------------------------------------------------
-- | The Plugin entrypoint ------------------------------------------------------
---------------------------------------------------------------------------------

plugin :: GHC.Plugin 
plugin = GHC.defaultPlugin {
    parsedResultAction = parseHook
  , typeCheckResultAction = typecheckHook
  , installCoreToDos = coreHook
  , dynflagsPlugin = customHooks
  , pluginRecompile = \_ -> pure NoForceRecompile
  , interfaceLoadAction = loadInterfaceHook
  }

-- | Overrides the default 'DynFlags' options. Specifically, we need the GHC
-- lexer not to throw away block comments, as this is where the LH spec comments
-- would live. This is why we set the 'Opt_KeepRawTokenStream' option.
customHooks :: [CommandLineOption] -> DynFlags -> IO DynFlags
customHooks opts dflags = do
  liftIO $ putStrLn "CustomHook"
  cfg <- liftIO $ LH.getOpts opts
  writeIORef cfgRef cfg
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
  let comments  = LH.extractSpecComments (hpm_annotations parsedModule)
  liftIO $ putStrLn $ "extractSpecComments ==> " ++ show comments

  commentsExps <- mapM (liftIO . TH.runQ . TH.liftData . SpecComment) comments

  let module' = parsedModule { 
      hpm_module = 
          fmap (specCommentsToModuleAnnotations (zip comments commentsExps)) 
               (hpm_module parsedModule) 
  }
  pure module'

specCommentsToModuleAnnotations :: [((SourcePos, String), TH.Exp)] 
                                -> HsModule GhcPs 
                                -> HsModule GhcPs
specCommentsToModuleAnnotations comments m = 
  m { hsmodDecls = map toAnnotation comments ++ hsmodDecls m }
  where
    toAnnotation :: ((SourcePos, String), TH.Exp) -> LHsDecl GhcPs
    toAnnotation ((pos, specContent), expr) = 
        let located = GHC.L (LH.sourcePosSrcSpan pos)
            hsExpr = either (throwGhcException . ProgramError . O.showSDocUnsafe) id $ 
                       convertToHsExpr (LH.sourcePosSrcSpan pos) expr
            annDecl = HsAnnotation @GhcPs noExtField Ghc.NoSourceText ModuleAnnProvenance hsExpr
        in located $ AnnD noExtField annDecl

--
-- Typechecking phase
--

-- | Currently we don't do anything in this phase.
typecheckHook :: [CommandLineOption] 
              -> ModSummary 
              -> TcGblEnv 
              -> TcM TcGblEnv
typecheckHook opts modSummary tcGblEnv = do
  let stableData = mkTcStableData tcGblEnv
  let thisModule = ms_mod modSummary

  -- Extend the 'ModuleEnv' held by the 'tcStableRef' with the data from this module.
  liftIO $ atomicModifyIORef' tcStableRef (\old -> (extendModuleEnv old thisModule stableData, ()))

  liftIO $ do
    readIORef testRef >>= (\x -> putStrLn $ "COUNTER ===> " ++ show x)
    atomicModifyIORef' testRef (\old -> (succ old, ()))

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
  hscEnv   <- getHscEnv
  specEnv  <- liftIO $ readIORef ifaceStableRef

  liftIO $ putStrLn $ "My UnitId = " ++ (O.showSDocUnsafe . O.ppr . moduleUnitId $ thisModule)

  liftIO $ putStrLn $ "Relevant ===> " ++ (unlines $ map (O.showSDocUnsafe . O.ppr) (relevantModules modGuts))

  -- Generate the bare-specs. Here we call 'extractSpecComments' which is what allows us to
  -- retrieve the 'SpecComment' information we computed in the 'parseHook' phase.
  let (guts', specComments) = Util.extractSpecComments modGuts
  let specQuotes = LH.extractSpecQuotes' mg_module mg_anns modGuts

  mbTcStableData <- (`lookupModuleEnv` thisModule) <$> liftIO (readIORef tcStableRef)
  let mbModSummary = mgLookupModule (hsc_mod_graph hscEnv) thisModule

  case (mbTcStableData, mbModSummary) of
    (Nothing, _) -> Util.pluginAbort dynFlags (O.text "No tcStableData found for " O.<+> O.ppr thisModule)
    (_, Nothing) -> Util.pluginAbort dynFlags (O.text "No modSummary found for " O.<+> O.ppr thisModule)
    (Just tcStableData, Just modSummary) -> do

     -- The targets of the current compilation. This list doesn't include dependencies of these targets.
     let targets = hsc_targets hscEnv
     logicMap <- liftIO $ LH.makeLogicMap

     let lhModGuts = LiquidHaskellModGuts {
           lhModuleCfg          = cfg
         , lhModuleLogicMap     = logicMap
         , lhModuleSummary      = modSummary
         , lhModuleTcStableData = tcStableData
         , lhModuleGuts         = guts'
         }

     -- Call into the interface
     thisFile <- liftIO $ canonicalizePath $ LH.modSummaryHsFile modSummary
     eps <- liftIO $ readIORef (hsc_EPS hscEnv)

     updatedSpecEnv <- loadRelevantSpecs cfg specEnv (relevantModules modGuts)
     (finalGuts, newSpecEnv, ghcInfo) <- processModule lhModGuts updatedSpecEnv specComments specQuotes
     res <- liftIO $ LH.liquidOne ghcInfo
     case o_result res of
       Safe -> pure ()
       _    -> pluginAbort dynFlags (O.text "Unsafe.")

     liftIO $ atomicModifyIORef' ifaceStableRef (\old -> (newSpecEnv, ()))

     liftIO $ print (map (O.showSDocUnsafe . O.ppr) $ mg_anns finalGuts)
     pure finalGuts


usedModules :: ModGuts -> [Module]
usedModules = foldl' collectUsage mempty . mg_usages
 where
   collectUsage :: [Module] -> Usage -> [Module]
   collectUsage acc = \case
     UsagePackageModule     { usg_mod = mod } -> mod : acc
     UsageMergedRequirement { usg_mod = mod } -> mod : acc
     _ -> acc

-- | The collection of dependencies and usages modules which are relevant for liquidHaskell
relevantModules :: ModGuts -> [Module]
relevantModules modGuts = 
 (map (toModule . fst) . filter (not . snd) . dep_mods $ deps) <> usedModules modGuts
 where
  deps :: Dependencies
  deps = mg_deps modGuts

  thisModule :: Module
  thisModule = mg_module modGuts

  toModule :: ModuleName -> Module
  toModule = Module (moduleUnitId thisModule)


data LiquidHaskellModGuts = LiquidHaskellModGuts {
    lhModuleCfg          :: Config
  , lhModuleLogicMap     :: LogicMap
  , lhModuleSummary      :: ModSummary
  , lhModuleTcStableData :: TcStableData
  , lhModuleGuts         :: ModGuts
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
    cfg <- liftIO getConfig
    liftIO $ putStrLn $ "loadInterfaceHook for " ++ (show . moduleName . mi_module $ iface)
    dynFlags <- getDynFlags
    specEnv <- liftIO $ readIORef ifaceStableRef

    sp <- runMaybeT (lookupCachedSpec specEnv thisModule <|> deserialiseFromAnnotations specEnv)
    case sp of
      Nothing -> pure ()
      Just (modName, spec)  -> do
        liftIO $ putStrLn $ "loadInterfaceHook, module found in SpecEnv..."
        liftIO $ atomicModifyIORef' ifaceStableRef (\old -> (extendModuleEnv old thisModule (modName, spec), ()))

    pure iface

  where
    thisModule :: Module
    thisModule = mi_module iface

    deserialiseFromAnnotations :: SpecEnv -> MaybeT (IfM lcl) (ModName, Ms.BareSpec)
    deserialiseFromAnnotations specEnv = do
      guard (not $ isHsBootOrSig $ mi_hsc_src iface)
      eps          <- lift getEps
      let bareSpecs = Util.deserialiseBareSpecs thisModule eps
      liftIO $ putStrLn $ "===spec==> " ++ show bareSpecs
      case bareSpecs of
        []         -> MaybeT $ pure Nothing
        [bareSpec] -> pure $ (ModName SrcImport (moduleName thisModule), bareSpec)
        specs      -> do
          dynFlags <- lift getDynFlags
          let msg = O.text "More than one spec file found for" 
                O.<+> O.ppr thisModule O.<+> O.text ":"
                O.<+> (O.vcat $ map (O.text . show) specs)
          lift $ pluginAbort dynFlags msg


lookupCachedSpec :: GhcMonadLike m => SpecEnv -> Module -> MaybeT m (ModName, Ms.BareSpec)
lookupCachedSpec specEnv mod = MaybeT $ pure (lookupModuleEnv specEnv mod)

-- | Load any relevant spec in the input 'SpecEnv', by updating it. The update will happen only if necessary,
-- i.e. if the spec is not already present.
loadRelevantSpecs :: forall m. GhcMonadLike m 
                  => Config 
                  -> SpecEnv 
                  -> [Module]
                  -> m SpecEnv
loadRelevantSpecs cfg specEnv = foldlM loadRelevantSpec specEnv 
  where
    loadRelevantSpec :: SpecEnv -> Module -> m SpecEnv
    loadRelevantSpec acc mod = do
      res <- runMaybeT (lookupCachedSpec acc mod <|> loadSpecFromDisk cfg acc mod)
      case res of
        Nothing -> do
          liftIO $ putStrLn $ "No spec found for " ++ show (moduleName mod)
          pure acc
        Just (modName, bareSpec) -> do
          liftIO $ putStrLn $ "Spec found for " ++ show (moduleName mod)
          pure $ extendModuleEnv acc mod (modName, bareSpec)

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
loadSpecFromDisk :: GhcMonadLike m 
                 => Config 
                 -> SpecEnv 
                 -> Module 
                 -> MaybeT m (ModName, Ms.BareSpec)
loadSpecFromDisk cfg specEnv thisModule = do
  env <- lift askHscEnv
  modSummary <- MaybeT $ pure (mgLookupModule (hsc_mod_graph env) thisModule)
  bareSpecs  <- lift $ findExternalSpecs cfg modSummary
  case bareSpecs of
    []         -> MaybeT $ pure Nothing
    [bareSpec] -> pure bareSpec
    specs      -> do
      dynFlags <- lift getDynFlags
      let msg = O.text "More than one spec file found for" 
            O.<+> O.ppr thisModule O.<+> O.text ":"
            O.<+> (O.vcat $ map (O.text . show) specs)
      lift $ pluginAbort dynFlags msg

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

updateIncludePaths :: DynFlags -> [FilePath] -> IncludeSpecs 
updateIncludePaths df ps = addGlobalInclude (includePaths df) ps 

configureDynFlags :: Config -> DynFlags -> IO DynFlags
configureDynFlags cfg df = do
  (df',_,_) <- parseDynamicFlags df $ map noLoc $ ghcOptions cfg
  let df'' = df' { importPaths  = nub $ idirs cfg ++ importPaths df'
                 , libraryPaths = nub $ idirs cfg ++ libraryPaths df'
                 , includePaths = updateIncludePaths df' (idirs cfg)
                 , packageFlags = ExposePackage ""
                                                (PackageArg "ghc-prim")
                                                (ModRenaming True [])
                                : (packageFlags df')

                 } `gopt_set` Opt_ImplicitImportQualified
                   `gopt_set` Opt_PIC
                   `gopt_set` Opt_DeferTypedHoles
                   `gopt_set` Opt_KeepRawTokenStream
                   `xopt_set` MagicHash
                   `xopt_set` DeriveGeneric
                   `xopt_set` StandaloneDeriving
  return df''

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

type SpecEnv = ModuleEnv (ModName, Ms.BareSpec)

processModule :: LiquidHaskellModGuts
              -> SpecEnv
              -> [SpecComment]
              -> [BPspec]
              -> CoreM (ModGuts, SpecEnv, GhcInfo)
processModule LiquidHaskellModGuts{..} specEnv specComments specQuotes = do
  let modGuts = lhModuleGuts
  Debug.traceShow ("Module ==> " ++ show (moduleName $ mg_module $ modGuts)) $ return ()
  let mod              = mg_module modGuts
  file                <- liftIO $ canonicalizePath $ LH.modSummaryHsFile lhModuleSummary
  (modName, bareSpec) <- either throw return $ hsSpecificationP (moduleName mod) (coerce specComments) specQuotes
  let specEnv'         = extendModuleEnv specEnv mod (modName, LH.noTerm bareSpec)

  -- Persist the 'BareSpec' in the final interface file by adding it as a new 'Annotation' to the 'ModGuts'.
  let modGuts'         = Util.serialiseBareSpecs [LH.noTerm bareSpec] modGuts

  (modGuts', specEnv', ) 
    <$> processTargetModule lhModuleCfg lhModuleLogicMap specEnv file lhModuleTcStableData lhModuleGuts bareSpec

processTargetModule :: Config 
                    -> LogicMap 
                    -> SpecEnv 
                    -> FilePath 
                    -> TcStableData
                    -> ModGuts
                    -> Ms.BareSpec
                    -> CoreM GhcInfo
processTargetModule cfg0 logicMap specEnv file tcStableData modGuts bareSpec = do
  hscEnv     <- getHscEnv
  cfg        <- liftIO $ withPragmas cfg0 file (Ms.pragmas bareSpec)
  ghcSrc     <- makeGhcSrc cfg file tcStableData modGuts hscEnv
  bareSpecs  <- makeBareSpecs cfg specEnv (moduleName $ mg_module modGuts) bareSpec
  let ghcSpec = makeGhcSpec   cfg ghcSrc  logicMap                         bareSpecs
  return      $ GI ghcSrc ghcSpec

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen 
---------------------------------------------------------------------------------------

makeGhcSrc :: GhcMonadLike m
           => Config
           -> FilePath 
           -> TcStableData
           -> ModGuts
           -> HscEnv
           -> m GhcSrc
makeGhcSrc cfg file tcStableData modGuts hscEnv = do
  let mgiModGuts    = makeMGIModGuts modGuts
  coreBinds         <- liftIO $ anormalize cfg hscEnv modGuts
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs mgiModGuts)
  (fiTcs, fiDcs)    <- liftIO $ LH.makeFamInstEnv hscEnv
  things            <- lookupTyThings hscEnv mgiModGuts
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
    , giDerVars   = S.fromList (LH.derivedVars cfg mgiModGuts)
    , gsExports   = mgi_exports  mgiModGuts
    , gsTcs       = mgi_tcs      mgiModGuts
    , gsCls       = mgi_cls_inst mgiModGuts
    , gsFiTcs     = fiTcs
    , gsFiDcs     = fiDcs
    , gsPrimTcs   = TysPrim.primTyCons
    , gsQualImps  = qualifiedImports tcStableData
    , gsAllImps   = allImports       tcStableData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }
  where
    makeMGIModGuts :: ModGuts -> MGIModGuts
    makeMGIModGuts modGuts = miModGuts deriv modGuts
      where
        deriv   = Just $ instEnvElts $ mg_inst_env modGuts

allImports :: TcStableData -> S.HashSet Symbol 
allImports tcStableData =
  S.fromList (symbol . unLoc . ideclName . unLoc <$> tcStableImports tcStableData) 

qualifiedImports :: TcStableData -> QImports 
qualifiedImports (tcStableImports -> imps) =
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
lookupTyThings :: GhcMonadLike m => HscEnv -> MGIModGuts -> m [(Name, Maybe TyThing)] 
lookupTyThings hscEnv mg =
  forM (mgNames mg) $ \n -> do 
    tt1 <-          GhcMonadLike.lookupName      n 
    tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n 
    -- tt3 <-          modInfoLookupName mi         n 
    tt4 <-          GhcMonadLike.lookupGlobalName n 
    return (n, Misc.firstMaybes [tt1, tt2, tt4])
  where
    mgNames :: MGIModGuts -> [Ghc.Name] 
    mgNames  = fmap Ghc.gre_name . Ghc.globalRdrEnvElts .  mgi_rdr_env 

---------------------------------------------------------------------------------------
-- | @makeBareSpecs@ loads BareSpec for target and imported modules 
---------------------------------------------------------------------------------------
makeBareSpecs :: GhcMonadLike m
              => Config 
              -> SpecEnv 
              -> ModuleName
              -> Ms.BareSpec 
              -> m [(ModName, Ms.BareSpec)]
makeBareSpecs cfg specEnv thisModule tgtSpec = do 
  modSum        <- GhcMonadLike.getModSummary thisModule
  externalSpecs <- findExternalSpecs cfg modSum
  let cachedSpecs = moduleEnvElts specEnv
  let allSpecs  = cachedSpecs <> externalSpecs
  let tgtMod    = ModName Target thisModule
  return        $ (tgtMod, tgtSpec) : allSpecs


findExternalSpecs :: GhcMonadLike m 
                  => Config 
                  -> ModSummary 
                  -> m [(ModName, Ms.BareSpec)]
findExternalSpecs cfg modSum =
  let paths = nub $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  in LH.findAndParseSpecFiles cfg paths modSum mempty -- reachable: mempty
