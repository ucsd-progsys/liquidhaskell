{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
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

import Data.Bifunctor
import Data.Coerce
import Data.Data
import Data.List hiding (intersperse)
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
import Language.Haskell.Liquid.Types hiding (Spec)
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.UX.Config (totalityCheck)
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.UX.Tidy
import Language.Fixpoint.Utils.Files

import qualified Debug.Trace as Debug 


tcStableRef :: IORef (ModuleEnv TcStableData)
tcStableRef = unsafePerformIO $ newIORef emptyModuleEnv
{-# NOINLINE tcStableRef #-}


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
  cfg <- liftIO $ LH.getOpts opts
  dflags' <- configureDynFlags cfg dflags
  return $ gopt_set dflags' Opt_KeepRawTokenStream

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
  let thisModule     = ms_mod modSummary

  -- Extend the 'ModuleEnv' held by the 'tcStableRef' with the data from this module.
  liftIO $ atomicModifyIORef' tcStableRef (\old -> (extendModuleEnv old thisModule stableData, ()))

  pure tcGblEnv

--
-- Core phase
--

coreHook :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
coreHook opts passes = do
  cfg <- liftIO $ LH.getOpts opts
  pure (CoreDoPluginPass "Language.Haskell.Liquid.GHC.Plugin" (liquidHaskellPass cfg) : passes)

-- | Partially calls into LiquidHaskell's GHC API.
liquidHaskellPass :: LH.Config -> ModGuts -> CoreM ModGuts
liquidHaskellPass cfg modGuts = do
  let thisModule = mg_module modGuts
  dynFlags <- getDynFlags
  env <- getHscEnv

  -- Generate the bare-specs. Here we call 'extractSpecComments' which is what allows us to
  -- retrieve the 'SpecComment' information we computed in the 'parseHook' phase.
  let (guts', specComments) = Util.extractSpecComments modGuts
  let specQuotes = LH.extractSpecQuotes' mg_module mg_anns modGuts

  mbTcStableData <- (`lookupModuleEnv` thisModule) <$> liftIO (readIORef tcStableRef)
  let mbModSummary = mgLookupModule (hsc_mod_graph env) thisModule

  case (mbTcStableData, mbModSummary) of
    (Nothing, _) -> Util.pluginAbort dynFlags (O.text "No tcStableData found for " O.<+> O.ppr thisModule)
    (_, Nothing) -> Util.pluginAbort dynFlags (O.text "No modSummary found for " O.<+> O.ppr thisModule)
    (Just tcStableData, Just modSummary) -> do

     -- The targets of the current compilation. This list doesn't include dependencies of these targets.
     let targets = hsc_targets env
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

     (_, mbGhcInfo) <- processModule lhModGuts (S.singleton thisFile) emptyModuleEnv specComments specQuotes
     case mbGhcInfo of
       Just info -> do
         res <- liftIO $ LH.liquidOne info
         case o_result res of
           Safe -> pure ()
           _    -> pluginAbort dynFlags (O.text "Unsafe.")
       Nothing   -> pure ()

     pure guts'


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
    liftIO $ print $ "loadInterfaceHook for " ++ (show . moduleName . mi_module $ iface)
    pure iface

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
                   `xopt_set` MagicHash
                   `xopt_set` DeriveGeneric
                   `xopt_set` StandaloneDeriving
  return df''

configureGhcTargets :: [FilePath] -> Ghc ModuleGraph
configureGhcTargets tgtFiles = do
  targets         <- mapM (`guessTarget` Nothing) tgtFiles
  _               <- setTargets targets
  moduleGraph     <- depanal [] False -- see [NOTE:DROP-BOOT-FILES]

  let homeModules  = filter (not . isBootSummary) $
                     flattenSCCs $ topSortModuleGraph False moduleGraph Nothing
  let homeNames    = moduleName . ms_mod <$> homeModules
  _               <- setTargetModules homeNames
  liftIO $ whenLoud $ print    ("Module Dependencies", homeNames)
  return $ mkModuleGraph homeModules

setTargetModules :: [ModuleName] -> Ghc ()
setTargetModules modNames = setTargets $ mkTarget <$> modNames
  where
    mkTarget modName = GHC.Target (TargetModule modName) True Nothing

compileCFiles :: Config -> Ghc ()
compileCFiles cfg = do
  df  <- getSessionDynFlags
  _   <- setSessionDynFlags $
           df { includePaths = updateIncludePaths df (idirs cfg) 
              , importPaths  = nub $ idirs cfg ++ importPaths df
              , libraryPaths = nub $ idirs cfg ++ libraryPaths df }
  hsc <- getSession
  os  <- mapM (\x -> liftIO $ compileFile hsc StopLn (x,Nothing)) (nub $ cFiles cfg)
  df  <- getSessionDynFlags
  void $ setSessionDynFlags $ df { ldInputs = nub $ map (FileOption "") os ++ ldInputs df }

{- | [NOTE:DROP-BOOT-FILES] Drop hs-boot files from the graph.
      We do it manually rather than using the flag to topSortModuleGraph
      because otherwise the order of mutually recursive modules depends
      on the modulename, e.g. given

      Bar.hs --> Foo.hs --> Bar.hs-boot

      we'll get
      
      [Bar.hs, Foo.hs]
    
      which is backwards..
 -}
--------------------------------------------------------------------------------
-- Home Module Dependency Graph ------------------------------------------------
--------------------------------------------------------------------------------

type DepGraph = Graph DepGraphNode
type DepGraphNode = Node Module ()

reachableModules :: DepGraph -> Module -> [Module]
reachableModules depGraph mod =
  node_key <$> tail (reachableG depGraph (DigraphNode () mod []))

buildDepGraph :: ModuleGraph -> Ghc DepGraph
buildDepGraph homeModules =
  graphFromEdgedVerticesOrd <$> mapM mkDepGraphNode (mgModSummaries homeModules)

mkDepGraphNode :: ModSummary -> Ghc DepGraphNode
mkDepGraphNode modSummary = 
  DigraphNode () (ms_mod modSummary) <$> (filterM isHomeModule =<< modSummaryImports modSummary)

isHomeModule :: Module -> Ghc Bool
isHomeModule mod = do
  homePkg <- thisPackage <$> getSessionDynFlags
  return   $ moduleUnitId mod == homePkg

modSummaryImports :: ModSummary -> Ghc [Module]
modSummaryImports modSummary =
  mapM (importDeclModule (ms_mod modSummary))
       (ms_textual_imps modSummary)

importDeclModule :: Module -> (Maybe FastString,  GHC.Located ModuleName) -> Ghc Module
importDeclModule fromMod (pkgQual, locModName) = do
  hscEnv <- getSession
  let modName = unLoc locModName
  result <- liftIO $ findImportedModule hscEnv modName pkgQual
  case result of
    Finder.Found _ mod -> return mod
    _ -> do
      dflags <- getSessionDynFlags
      liftIO $ throwGhcExceptionIO $ ProgramError $
        O.showPpr dflags (moduleName fromMod) ++ ": " ++
        O.showSDoc dflags (cannotFindModule dflags modName result)

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

type SpecEnv = ModuleEnv (ModName, Ms.BareSpec)

--processModules :: TcStableData
--               -> Config 
--               -> LogicMap 
--               -> [FilePath] 
--               -> DepGraph 
--               -> ModuleGraph 
--               -> CoreM [GhcInfo]
--processModules tcStableData cfg logicMap tgtFiles depGraph homeModules = do
--  -- DO NOT DELETE: liftIO $ putStrLn $ "Process Modules: TargetFiles = " ++ show tgtFiles
--  catMaybes . snd <$> Misc.mapAccumM go emptyModuleEnv (mgModSummaries homeModules)
--  where
--    go = processModule tcStableData cfg logicMap (S.fromList tgtFiles) depGraph

processModule :: LiquidHaskellModGuts
              -> S.HashSet FilePath
              -> SpecEnv
              -> [SpecComment]
              -> [BPspec]
              -> CoreM (SpecEnv, Maybe GhcInfo)
processModule LiquidHaskellModGuts{..} targets specEnv specComments specQuotes = do
  let modGuts = lhModuleGuts
  Debug.traceShow ("Module ==> " ++ show (moduleName $ mg_module $ modGuts)) $ return ()
  let mod              = mg_module modGuts
  file                <- liftIO $ canonicalizePath $ modSummaryHsFile lhModuleSummary
  let isTarget         = file `S.member` targets
  (modName, commSpec) <- either throw return $ 
    hsSpecificationP (moduleName mod) (coerce specComments) specQuotes
  liftedSpec          <- liftIO $ if isTarget || null specComments then return Nothing 
                                                                   else loadLiftedSpec lhModuleCfg file 
  let bareSpec         = updLiftedSpec commSpec liftedSpec
  let specEnv'         = extendModuleEnv specEnv mod (modName, noTerm bareSpec)
  (specEnv', ) <$> if isTarget
                     then Just <$> processTargetModule lhModuleCfg lhModuleLogicMap specEnv file lhModuleTcStableData lhModuleGuts bareSpec
                     else return Nothing

updLiftedSpec :: Ms.BareSpec -> Maybe Ms.BareSpec -> Ms.BareSpec 
updLiftedSpec s1 Nothing   = s1 
updLiftedSpec s1 (Just s2) = (clear s1) `mappend` s2 
  where 
    clear s                = s { sigs = [], aliases = [], ealiases = [], qualifiers = [], dataDecls = [] }

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
  ghcSrc     <- liftIO $ makeGhcSrc cfg file tcStableData modGuts hscEnv
  bareSpecs  <- makeBareSpecs' cfg specEnv modGuts bareSpec
  let ghcSpec = makeGhcSpec    cfg ghcSrc   logicMap        bareSpecs
  -- ghc: panic! (the 'impossible' happened)
  -- (GHC version 8.10.0.20191210:
  --       [LH.Bare.listTyDataCons:0:0: Error: Illegal data refinement for `[]`
  --   Size function len x should have type int.
  --   Unbound symbol len --- perhaps you meant: head, x ?]
  -- _          <- liftIO $ saveLiftedSpec ghcSrc ghcSpec -- TODO(and) Persist as an annotation in the interface.
  return      $ GI ghcSrc ghcSpec

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen 
---------------------------------------------------------------------------------------

makeGhcSrc :: Config
           -> FilePath 
           -> TcStableData
           -> ModGuts
           -> HscEnv
           -> IO GhcSrc
makeGhcSrc cfg file tcStableData modGuts hscEnv = do
  let mgiModGuts    = makeMGIModGuts modGuts
  coreBinds         <- anormalize cfg hscEnv modGuts
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs mgiModGuts)
  (fiTcs, fiDcs)    <- makeFamInstEnv hscEnv
  things            <- lookupTyThings' hscEnv mgiModGuts
  let impVars        = LH.importVars coreBinds ++ LH.classCons (mgi_cls_inst mgiModGuts)
  incDir            <- Misc.getIncludeDir
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
    , gsQualImps  = qualifiedImports' tcStableData
    , gsAllImps   = allImports'       tcStableData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }

allImports' :: TcStableData -> S.HashSet Symbol 
allImports' tcStableData =
  S.fromList (symbol . unLoc . ideclName . unLoc <$> tcStableImports tcStableData) 

qualifiedImports' :: TcStableData -> QImports 
qualifiedImports' (tcStableImports -> imps) =
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
lookupTyThings :: HscEnv -> TypecheckedModule -> MGIModGuts -> Ghc [(Name, Maybe TyThing)] 
lookupTyThings hscEnv tcm mg =
  forM (mgNames mg) $ \n -> do 
    tt1 <-          lookupName                   n 
    tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n 
    tt3 <-          modInfoLookupName mi         n 
    tt4 <-          lookupGlobalName             n 
    return (n, Misc.firstMaybes [tt1, tt2, tt3, tt4])
    where 
      mi = tm_checked_module_info tcm

lookupTyThings' :: HscEnv -> MGIModGuts -> IO [(Name, Maybe TyThing)] 
lookupTyThings' hscEnv mg =
  forM (mgNames mg) $ \n -> do 
    -- TODO: lookup in the current module
    mbTy <- lookupTypeHscEnv hscEnv n
    return (n, mbTy)

mgNames :: MGIModGuts -> [Ghc.Name] 
mgNames  = fmap Ghc.gre_name . Ghc.globalRdrEnvElts .  mgi_rdr_env 

---------------------------------------------------------------------------------------
-- | @makeBareSpecs@ loads BareSpec for target and imported modules 
---------------------------------------------------------------------------------------
{-
makeBareSpecs :: Config 
              -> DepGraph 
              -> SpecEnv 
              -> ModSummary 
              -> Ms.BareSpec 
              -> Ghc [(ModName, Ms.BareSpec)]
makeBareSpecs cfg depGraph specEnv modSum tgtSpec = do 
  let paths     = nub $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  _            <- liftIO $ whenLoud $ putStrLn $ "paths = " ++ show paths
  let reachable = reachableModules depGraph (ms_mod modSum)
  specSpecs    <- LH.findAndParseSpecFiles cfg paths modSum reachable
  let homeSpecs = cachedBareSpecs specEnv reachable
  let impSpecs  = specSpecs ++ homeSpecs
  let tgtMod    = ModName Target (moduleName (ms_mod modSum))
  return        $ (tgtMod, tgtSpec) : impSpecs
-}

-- This will use annotations to return the specs.
makeBareSpecs' :: Config 
               -> SpecEnv
               -> ModGuts
               -> Ms.BareSpec 
               -> CoreM [(ModName, Ms.BareSpec)]
makeBareSpecs' cfg specEnv modGuts tgtSpec = do
  let tgtMod = ModName Target (moduleName (mg_module modGuts))

  -- NOTE(adn) Consider also 'dep_pkgs'?
  dependenciesSpecs <- foldlM getSpec mempty (dep_mods $ mg_deps modGuts)

  pure $ (tgtMod, tgtSpec) : dependenciesSpecs

  where
    getSpec :: [(ModName, Ms.BareSpec)] -> (ModuleName, IsBootInterface) -> CoreM [(ModName, Ms.BareSpec)]
    getSpec !allSpecs (_, True)        = pure allSpecs
    getSpec !allSpecs (modName, False) = pure allSpecs

modSummaryHsFile :: ModSummary -> FilePath
modSummaryHsFile modSummary =
  fromMaybe
    (panic Nothing $
      "modSummaryHsFile: missing .hs file for " ++
      showPpr (ms_mod modSummary))
    (ml_hs_file $ ms_location modSummary)

cachedBareSpecs :: SpecEnv -> [Module] -> [(ModName, Ms.BareSpec)]
cachedBareSpecs specEnv mods = lookupBareSpec <$> mods
  where
    lookupBareSpec m         = fromMaybe (err m) (lookupModuleEnv specEnv m)
    err m                    = impossible Nothing ("lookupBareSpec: missing module " ++ showPpr m)

--------------------------------------------------------------------------------
-- | Family instance information
--------------------------------------------------------------------------------
makeFamInstEnv :: HscEnv -> IO ([GHC.TyCon], [(Symbol, DataCon)])
makeFamInstEnv env = do
  famInsts <- getFamInstances env
  let fiTcs = [ tc            | FamInst { fi_flavor = DataFamilyInst tc } <- famInsts ]
  let fiDcs = [ (symbol d, d) | tc <- fiTcs, d <- tyConDataCons tc ]
  return (fiTcs, fiDcs)

getFamInstances :: HscEnv -> IO [FamInst]
getFamInstances env = do
  (_, Just (pkg_fie, home_fie)) <- runTcInteractive env tcGetFamInstEnvs
  return $ famInstEnvElts home_fie ++ famInstEnvElts pkg_fie
 
refreshSymbols :: Data a => a -> a
refreshSymbols = everywhere (mkT refreshSymbol)

refreshSymbol :: Symbol -> Symbol
refreshSymbol = symbol . symbolText

--------------------------------------------------------------------------------
-- | Finding & Parsing Files ---------------------------------------------------
--------------------------------------------------------------------------------

getPatSpec :: [FilePath] -> Bool -> Ghc [FilePath]
getPatSpec paths totalitycheck
 | totalitycheck = moduleFiles Spec paths [patErrorName]
 | otherwise     = return []
 where
  patErrorName   = "PatErr"

getRealSpec :: [FilePath] -> Bool -> Ghc [FilePath]
getRealSpec paths freal
  | freal     = moduleFiles Spec paths [realSpecName]
  | otherwise = moduleFiles Spec paths [notRealSpecName]
  where
    realSpecName    = "Real"
    notRealSpecName = "NotReal"

transParseSpecs :: [FilePath]
                -> S.HashSet FilePath 
                -> [(ModName, Ms.BareSpec)]
                -> [FilePath]
                -> Ghc [(ModName, Ms.BareSpec)]
transParseSpecs _ _ specs [] = return specs
transParseSpecs paths seenFiles specs newFiles = do
  newSpecs      <- liftIO $ mapM parseSpecFile newFiles
  impFiles      <- moduleFiles Spec paths $ specsImports newSpecs
  let seenFiles' = seenFiles `S.union` S.fromList newFiles
  let specs'     = specs ++ map (second noTerm) newSpecs
  let newFiles'  = filter (not . (`S.member` seenFiles')) impFiles
  transParseSpecs paths seenFiles' specs' newFiles'
  where
    specsImports ss = nub $ concatMap (map symbolString . Ms.imports . snd) ss

noTerm :: Ms.BareSpec -> Ms.BareSpec
noTerm spec = spec { Ms.decr = mempty, Ms.lazy = mempty, Ms.termexprs = mempty }

parseSpecFile :: FilePath -> IO (ModName, Ms.BareSpec)
parseSpecFile file = either throw return . specSpecificationP file =<< Misc.sayReadFile file

-- Find Files for Modules ------------------------------------------------------

moduleFiles :: Ext -> [FilePath] -> [String] -> Ghc [FilePath]
moduleFiles ext paths names = catMaybes <$> mapM (moduleFile ext paths) names

moduleFile :: Ext -> [FilePath] -> String -> Ghc (Maybe FilePath)
moduleFile ext paths name
  | ext `elem` [Hs, LHs] = do
    graph <- mgModSummaries <$> getModuleGraph
    case find (\m -> not (isBootSummary m) &&
                     name == moduleNameString (ms_mod_name m)) graph of
      Nothing -> liftIO $ getFileInDirs (extModuleName name ext) paths
      Just ms -> return $ normalise <$> ml_hs_file (ms_location ms)
  | otherwise = liftIO $ getFileInDirs (extModuleName name ext) paths

--------------------------------------------------------------------------------
-- Assemble Information for Spec Extraction ------------------------------------
--------------------------------------------------------------------------------

makeMGIModGuts :: ModGuts -> MGIModGuts
makeMGIModGuts modGuts = miModGuts deriv modGuts
  where
    deriv   = Just $ instEnvElts $ mg_inst_env modGuts

makeLogicMap :: IO LogicMap
makeLogicMap = do
  lg    <- Misc.getCoreToLogicPath
  lspec <- Misc.sayReadFile lg
  case parseSymbolToLogic lg lspec of 
    Left e   -> throw e 
    Right lm -> return (lm <> listLMap)

listLMap :: LogicMap -- TODO-REBARE: move to wiredIn
listLMap  = toLogicMap [ (dummyLoc nilName , []     , hNil)
                       , (dummyLoc consName, [x, xs], hCons (EVar <$> [x, xs])) ]
  where
    x     = "x"
    xs    = "xs"
    hNil  = mkEApp (dcSym Ghc.nilDataCon ) []
    hCons = mkEApp (dcSym Ghc.consDataCon)
    dcSym = dummyLoc . dropModuleUnique . symbol
