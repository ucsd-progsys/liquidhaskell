{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE ViewPatterns               #-}

module Language.Haskell.Liquid.GHC.Interface (

  -- * Determine the build-order for target files
   realTargets

  -- * Extract all information needed for verification
  , getGhcInfos
  , runLiquidGhc

  -- * Printer
  , pprintCBs

  -- * predicates
  -- , isExportedVar
  -- , exportedVars

  -- * Internal exports (provisional)
  , extractSpecComments
  , extractSpecQuotes'
  , makeLogicMap
  , classCons
  , derivedVars
  , importVars
  , makeGhcSrc
  , qImports
  , modSummaryHsFile
  , makeFamInstEnv
  , findAndParseSpecFiles
  , parseSpecFile
  , noTerm
  , checkFilePragmas
  , keepRawTokenStream
  , ignoreInline
  , lookupTyThings

  ) where

import Prelude hiding (error)

import qualified Outputable as O
import GHC hiding (Target, Located, desugarModule)
import qualified GHC
import GHC.Paths (libdir)
import GHC.Serialized

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
import Panic (throwGhcExceptionIO)
-- import Serialized
import TcRnTypes
import Var
-- import NameSet
import FastString
import FamInstEnv
import FamInst
import qualified TysPrim
import GHC.LanguageExtensions

import Control.Exception
import Control.Monad
import Control.Monad.IO.Class

import Data.Bifunctor
import Data.Data
import Data.List hiding (intersperse)
import Data.Maybe

import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import qualified Data.HashSet        as S
import qualified Data.Map            as M

import System.Console.CmdArgs.Verbosity hiding (Loud)
import System.Directory
import System.FilePath
import System.IO.Temp
import Text.Parsec.Pos
import Text.PrettyPrint.HughesPJ        hiding (first, (<>))
import Language.Fixpoint.Types          hiding (panic, Error, Result, Expr)
import qualified Language.Fixpoint.Misc as Misc
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.GHC.Play
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike
import Language.Haskell.Liquid.GHC.GhcMonadLike (GhcMonadLike, askHscEnv)
import Language.Haskell.Liquid.WiredIn (isDerivedInstance) 
import qualified Language.Haskell.Liquid.Measure  as Ms
import qualified Language.Haskell.Liquid.Misc     as Misc
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Types hiding (Spec)
-- import Language.Haskell.Liquid.Types.PrettyPrint
-- import Language.Haskell.Liquid.Types.Visitors
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.UX.Config (totalityCheck)
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.UX.Tidy
import Language.Fixpoint.Utils.Files

import qualified Debug.Trace as Debug 


--------------------------------------------------------------------------------
{- | @realTargets mE cfg targets@ uses `Interface.configureGhcTargets` to 
     return a list of files

       [i1, i2, ... ] ++ [f1, f2, ...]

     1. Where each file only (transitively imports) PRECEDIING ones; 
     2. `f1..` are a permutation of the original `targets`;
     3. `i1..` either don't have "fresh" .bspec files. 

 -}
--------------------------------------------------------------------------------
realTargets :: Maybe HscEnv -> Config -> [FilePath] -> IO [FilePath] 
realTargets  mbEnv cfg tgtFs 
  | noCheckImports cfg = return tgtFs
  | otherwise          = do 
    incDir   <- Misc.getIncludeDir 
    allFs    <- orderTargets mbEnv cfg tgtFs
    let srcFs = filter (not . Misc.isIncludeFile incDir) allFs
    realFs   <- filterM check srcFs
    dir      <- getCurrentDirectory
    return      (makeRelative dir <$> realFs)
  where 
    check f    = not <$> skipTarget tgts f 
    tgts       = S.fromList tgtFs

orderTargets :: Maybe HscEnv -> Config -> [FilePath] -> IO [FilePath] 
orderTargets mbEnv cfg tgtFiles = runLiquidGhc mbEnv cfg $ do 
  homeModules <- configureGhcTargets tgtFiles
  return         (modSummaryHsFile <$> mgModSummaries homeModules)


skipTarget :: S.HashSet FilePath -> FilePath -> IO Bool
skipTarget tgts f 
  | S.member f tgts = return False          -- Always check target file 
  | otherwise       = hasFreshBinSpec f     -- But skip an import with fresh .bspec

hasFreshBinSpec :: FilePath -> IO Bool
hasFreshBinSpec srcF = do 
  let specF = extFileName BinSpec srcF
  srcMb    <- Misc.lastModified srcF 
  specMb   <- Misc.lastModified specF 
  case (srcMb, specMb) of 
    (Just srcT, Just specT) -> return (srcT < specT)
    _                       -> return False



--------------------------------------------------------------------------------
-- | GHC Interface Pipeline ----------------------------------------------------
--------------------------------------------------------------------------------

getGhcInfos :: Maybe HscEnv -> Config -> [FilePath] -> IO ([GhcInfo], HscEnv)
getGhcInfos hscEnv cfg tgtFiles' = do
  tgtFiles <- mapM canonicalizePath tgtFiles'
  _        <- mapM checkFilePresent tgtFiles
  _        <- mapM_ createTempDirectoryIfMissing tgtFiles
  logicMap <- liftIO makeLogicMap
  runLiquidGhc hscEnv cfg (getGhcInfos' cfg logicMap tgtFiles)

checkFilePresent :: FilePath -> IO ()
checkFilePresent f = do
  b <- doesFileExist f
  unless b $ panic Nothing ("Cannot find file: " ++ f)

getGhcInfos' :: Config -> LogicMap -> [FilePath] -> Ghc ([GhcInfo], HscEnv)
getGhcInfos' cfg logicMap tgtFiles = do
  _           <- compileCFiles cfg
  homeModules <- configureGhcTargets tgtFiles
  depGraph    <- buildDepGraph homeModules
  ghcInfos    <- processModules cfg logicMap tgtFiles depGraph homeModules
  hscEnv      <- getSession
  return (ghcInfos, hscEnv)

createTempDirectoryIfMissing :: FilePath -> IO ()
createTempDirectoryIfMissing tgtFile = Misc.tryIgnore "create temp directory" $
  createDirectoryIfMissing False $ tempDirectory tgtFile

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------
runLiquidGhc :: Maybe HscEnv -> Config -> Ghc a -> IO a
runLiquidGhc hscEnv cfg act =
  withSystemTempDirectory "liquid" $ \tmp ->
    runGhc (Just libdir) $ do
      maybe (return ()) setSession hscEnv
      df <- configureDynFlags cfg tmp
      prettyPrintGhcErrors df act

updateIncludePaths :: DynFlags -> [FilePath] -> IncludeSpecs 
updateIncludePaths df ps = addGlobalInclude (includePaths df) ps 

configureDynFlags :: Config -> FilePath -> Ghc DynFlags
configureDynFlags cfg tmp = do
  df <- getSessionDynFlags
  (df',_,_) <- parseDynamicFlags df $ map noLoc $ ghcOptions cfg
  loud <- liftIO isLoud
  let df'' = df' { importPaths  = nub $ idirs cfg ++ importPaths df'
                 , libraryPaths = nub $ idirs cfg ++ libraryPaths df'
                 , includePaths = updateIncludePaths df' (idirs cfg) -- addGlobalInclude (includePaths df') (idirs cfg) 
                 , packageFlags = ExposePackage ""
                                                (PackageArg "ghc-prim")
                                                (ModRenaming True [])
                                : (packageFlags df')

                 , debugLevel   = 1               -- insert SourceNotes
                 -- , profAuto     = ProfAutoCalls
                 , ghcLink      = LinkInMemory
                 , hscTarget    = HscInterpreted
                 , ghcMode      = CompManager
                 -- prevent GHC from printing anything, unless in Loud mode
                 , log_action   = if loud
                                    then defaultLogAction
                                    else \_ _ _ _ _ _ -> return ()
                 -- redirect .hi/.o/etc files to temp directory
                 , objectDir    = Just tmp
                 , hiDir        = Just tmp
                 , stubDir      = Just tmp
                 } `gopt_set` Opt_ImplicitImportQualified
                   `gopt_set` Opt_PIC
                   `gopt_set` Opt_DeferTypedHoles
                   `xopt_set` MagicHash
                   `xopt_set` DeriveGeneric
                   `xopt_set` StandaloneDeriving
  _ <- setSessionDynFlags df''
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

isHomeModule :: GhcMonadLike m => Module -> m Bool
isHomeModule mod = do
  homePkg <- thisPackage <$> getDynFlags
  return   $ moduleUnitId mod == homePkg

modSummaryImports :: GhcMonadLike m => ModSummary -> m [Module]
modSummaryImports modSummary =
  mapM (importDeclModule (ms_mod modSummary))
       (ms_textual_imps modSummary)

importDeclModule :: GhcMonadLike m => Module -> (Maybe FastString,  GHC.Located ModuleName) -> m Module
importDeclModule fromMod (pkgQual, locModName) = do
  hscEnv <- askHscEnv
  let modName = unLoc locModName
  result <- liftIO $ findImportedModule hscEnv modName pkgQual
  case result of
    Finder.Found _ mod -> return mod
    _ -> do
      dflags <- getDynFlags
      liftIO $ throwGhcExceptionIO $ ProgramError $
        O.showPpr dflags (moduleName fromMod) ++ ": " ++
        O.showSDoc dflags (cannotFindModule dflags modName result)

--------------------------------------------------------------------------------
-- | Extract Ids ---------------------------------------------------------------
--------------------------------------------------------------------------------

classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: Config -> MGIModGuts -> [Var]  
derivedVars cfg mg  = concatMap (dFunIdVars cbs . is_dfun) derInsts 
  where 
    derInsts        
      | checkDer    = insts 
      | otherwise   = filter isDerivedInstance insts
    insts           = mgClsInstances mg 
    checkDer        = checkDerived cfg
    cbs             = mgi_binds mg
               

mgClsInstances :: MGIModGuts -> [ClsInst]
mgClsInstances = fromMaybe [] . mgi_cls_inst 

dFunIdVars :: CoreProgram -> DFunId -> [Id]
dFunIdVars cbs fd  = notracepp msg $ concatMap bindersOf cbs' ++ deps
  where
    msg            = "DERIVED-VARS-OF: " ++ showpp fd
    cbs'           = filter f cbs
    f (NonRec x _) = eqFd x
    f (Rec xes)    = any eqFd (fst <$> xes)
    eqFd x         = varName x == varName fd
    deps           = concatMap unfoldDep unfolds
    unfolds        = unfoldingInfo . idInfo <$> concatMap bindersOf cbs'

unfoldDep :: Unfolding -> [Id]
unfoldDep (DFunUnfolding _ _ e)       = concatMap exprDep e
unfoldDep CoreUnfolding {uf_tmpl = e} = exprDep e
unfoldDep _                           = []

exprDep :: CoreExpr -> [Id]
exprDep = freeVars S.empty

importVars :: CoreProgram -> [Id]
importVars = freeVars S.empty

_definedVars :: CoreProgram -> [Id]
_definedVars = concatMap defs
  where
    defs (NonRec x _) = [x]
    defs (Rec xes)    = map fst xes

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

type SpecEnv = ModuleEnv (ModName, Ms.BareSpec)

processModules :: Config -> LogicMap -> [FilePath] -> DepGraph -> ModuleGraph -> Ghc [GhcInfo]
processModules cfg logicMap tgtFiles depGraph homeModules = do
  -- DO NOT DELETE: liftIO $ putStrLn $ "Process Modules: TargetFiles = " ++ show tgtFiles
  catMaybes . snd <$> Misc.mapAccumM go emptyModuleEnv (mgModSummaries homeModules)
  where                                             
    go = processModule cfg logicMap (S.fromList tgtFiles) depGraph

processModule :: Config -> LogicMap -> S.HashSet FilePath -> DepGraph -> SpecEnv -> ModSummary
              -> Ghc (SpecEnv, Maybe GhcInfo)
processModule cfg logicMap tgtFiles depGraph specEnv modSummary = do
  let mod              = ms_mod modSummary
  -- DO-NOT-DELETE _                <- liftIO $ whenLoud $ putStrLn $ "Process Module: " ++ showPpr (moduleName mod)
  file                <- liftIO $ canonicalizePath $ modSummaryHsFile modSummary
  let isTarget         = Debug.traceShowId file `S.member` tgtFiles
  _                   <- loadDependenciesOf $ moduleName mod
  parsed              <- parseModule $ keepRawTokenStream modSummary
  let specComments     = extractSpecComments (pm_annotations parsed)
  typechecked         <- typecheckModule $ ignoreInline parsed
  let specQuotes       = extractSpecQuotes typechecked
  _                   <- loadModule' typechecked
  (modName, commSpec) <- either throw return $ hsSpecificationP (moduleName mod) specComments specQuotes
  liftedSpec          <- liftIO $ if isTarget || null specComments then return Nothing else loadLiftedSpec cfg file 
  let bareSpec         = updLiftedSpec commSpec liftedSpec
  _                   <- checkFilePragmas $ Ms.pragmas bareSpec
  let specEnv'         = extendModuleEnv specEnv mod (modName, noTerm bareSpec)
  (specEnv', ) <$> if isTarget
                     then Just <$> processTargetModule cfg logicMap depGraph specEnv file typechecked bareSpec
                     else return Nothing

updLiftedSpec :: Ms.BareSpec -> Maybe Ms.BareSpec -> Ms.BareSpec 
updLiftedSpec s1 Nothing   = s1 
updLiftedSpec s1 (Just s2) = (clear s1) `mappend` s2 
  where 
    clear s                = s { sigs = [], aliases = [], ealiases = [], qualifiers = [], dataDecls = [] }

keepRawTokenStream :: ModSummary -> ModSummary
keepRawTokenStream modSummary = modSummary
  { ms_hspp_opts = ms_hspp_opts modSummary `gopt_set` Opt_KeepRawTokenStream }

loadDependenciesOf :: ModuleName -> Ghc ()
loadDependenciesOf modName = do
  loadResult <- load $ LoadDependenciesOf modName
  when (failed loadResult) $ liftIO $ throwGhcExceptionIO $ ProgramError $
   "Failed to load dependencies of module " ++ showPpr modName

loadModule' :: TypecheckedModule -> Ghc TypecheckedModule
loadModule' tm = loadModule tm'
  where
    pm   = tm_parsed_module tm
    ms   = pm_mod_summary pm
    df   = ms_hspp_opts ms
    df'  = df { hscTarget = HscNothing, ghcLink = NoLink }
    ms'  = ms { ms_hspp_opts = df' }
    pm'  = pm { pm_mod_summary = ms' }
    tm'  = tm { tm_parsed_module = pm' }


processTargetModule :: Config -> LogicMap -> DepGraph -> SpecEnv -> FilePath -> TypecheckedModule -> Ms.BareSpec
                    -> Ghc GhcInfo
processTargetModule cfg0 logicMap depGraph specEnv file typechecked bareSpec = do
  cfg        <- liftIO $ withPragmas cfg0 file (Ms.pragmas bareSpec)
  let modSum  = pm_mod_summary (tm_parsed_module typechecked)
  ghcSrc     <- makeGhcSrc    cfg file     typechecked modSum
  bareSpecs  <- makeBareSpecs cfg depGraph specEnv     modSum bareSpec
  let ghcSpec = makeGhcSpec   cfg ghcSrc   logicMap           bareSpecs  
  _          <- liftIO $ saveLiftedSpec ghcSrc ghcSpec 
  return      $ GI ghcSrc ghcSpec

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen 
---------------------------------------------------------------------------------------

makeGhcSrc :: Config -> FilePath -> TypecheckedModule -> ModSummary -> Ghc GhcSrc 
makeGhcSrc cfg file typechecked modSum = do
  desugared         <- desugarModule  typechecked
  let modGuts'       = dm_core_module desugared
  let modGuts        = makeMGIModGuts modGuts'
  hscEnv            <- getSession
  coreBinds         <- liftIO $ anormalize cfg hscEnv modGuts'
  _                 <- liftIO $ whenNormal $ Misc.donePhase Misc.Loud "A-Normalization"
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs modGuts)
  (fiTcs, fiDcs)    <- liftIO $ makeFamInstEnv hscEnv 
  things            <- lookupTyThings hscEnv modSum (fst $ tm_internals_ typechecked)
  let impVars        = importVars coreBinds ++ classCons (mgi_cls_inst modGuts)
  incDir            <- liftIO $ Misc.getIncludeDir
  return $ Src 
    { giIncDir    = incDir 
    , giTarget    = file
    , giTargetMod = ModName Target (moduleName (ms_mod modSum))
    , giCbs       = coreBinds
    , giImpVars   = impVars 
    , giDefVars   = dataCons ++ (letVars coreBinds) 
    , giUseVars   = readVars coreBinds
    , giDerVars   = S.fromList (derivedVars cfg modGuts) 
    , gsExports   = mgi_exports  modGuts 
    , gsTcs       = mgi_tcs      modGuts
    , gsCls       = mgi_cls_inst modGuts 
    , gsFiTcs     = fiTcs 
    , gsFiDcs     = fiDcs
    , gsPrimTcs   = TysPrim.primTyCons
    , gsQualImps  = qualifiedImports typechecked 
    , gsAllImps   = allImports       typechecked
    , gsTyThings  = [ t | (_, Just t) <- things ] 
    }

_impThings :: [Var] -> [TyThing] -> [TyThing]
_impThings vars  = filter ok
  where
    vs          = S.fromList vars 
    ok (AnId x) = S.member x vs  
    ok _        = True 

allImports :: TypecheckedModule -> S.HashSet Symbol 
allImports tm = case tm_renamed_source tm of 
  Nothing           -> Debug.trace "WARNING: Missing RenamedSource" mempty 
  Just (_,imps,_,_) -> S.fromList (symbol . unLoc . ideclName . unLoc <$> imps)

qualifiedImports :: TypecheckedModule -> QImports 
qualifiedImports tm = case tm_renamed_source tm of 
  Nothing           -> Debug.trace "WARNING: Missing RenamedSource" (qImports mempty) 
  Just (_,imps,_,_) -> qImports [ (qn, n) | i         <- imps
                                          , let decl   = unLoc i
                                          , let m      = unLoc (ideclName decl)  
                                          , qm        <- maybeToList (unLoc <$> ideclAs decl) 
                                          , let [n,qn] = symbol <$> [m, qm] 
                                          ]

qImports :: [(Symbol, Symbol)] -> QImports 
qImports qns  = QImports 
  { qiNames   = Misc.group qns 
  , qiModules = S.fromList (snd <$> qns) 
  }


---------------------------------------------------------------------------------------
-- | @lookupTyThings@ grabs all the @Name@s and associated @TyThing@ known to GHC 
--   for this module; we will use this to create our name-resolution environment 
--   (see `Bare.Resolve`)                                          
---------------------------------------------------------------------------------------
lookupTyThings :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> m [(Name, Maybe TyThing)]
lookupTyThings hscEnv modSum tcGblEnv = do
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

-- lookupName        :: GhcMonad m => Name -> m (Maybe TyThing) 
-- hscTcRcLookupName :: HscEnv -> Name -> IO (Maybe TyThing)
-- modInfoLookupName :: GhcMonad m => ModuleInfo -> Name -> m (Maybe TyThing)  
-- lookupGlobalName  :: GhcMonad m => Name -> m (Maybe TyThing)  

_dumpTypeEnv :: TypecheckedModule -> IO () 
_dumpTypeEnv tm = do 
  print "DUMP-TYPE-ENV"
  print (showpp <$> tcmTyThings tm)

tcmTyThings :: TypecheckedModule -> Maybe [Name] 
tcmTyThings 
  = id 
  -- typeEnvElts 
  -- . tcg_type_env . fst 
  -- . md_types . snd
  -- . tm_internals_
  . modInfoTopLevelScope
  . tm_checked_module_info


_dumpRdrEnv :: HscEnv -> MGIModGuts -> IO () 
_dumpRdrEnv _hscEnv modGuts = do 
  print "DUMP-RDR-ENV" 
  print (mgNames modGuts)
  -- print (hscNames hscEnv) 
  -- print (mgDeps modGuts) 
  where 
    _mgDeps   = Ghc.dep_mods . mgi_deps 
    _hscNames = fmap showPpr . Ghc.ic_tythings . Ghc.hsc_IC

mgNames :: MGIModGuts -> [Ghc.Name] 
mgNames  = fmap Ghc.gre_name . Ghc.globalRdrEnvElts .  mgi_rdr_env 

---------------------------------------------------------------------------------------
-- | @makeBareSpecs@ loads BareSpec for target and imported modules 
---------------------------------------------------------------------------------------
makeBareSpecs :: Config -> DepGraph -> SpecEnv -> ModSummary -> Ms.BareSpec 
              -> Ghc [(ModName, Ms.BareSpec)]
makeBareSpecs cfg depGraph specEnv modSum tgtSpec = do 
  let paths     = S.fromList $ idirs cfg ++ importPaths (ms_hspp_opts modSum)
  _            <- liftIO $ whenLoud $ putStrLn $ "paths = " ++ show paths
  let reachable = reachableModules depGraph (ms_mod modSum)
  specSpecs    <- findAndParseSpecFiles cfg paths modSum reachable
  let homeSpecs = cachedBareSpecs specEnv reachable
  let impSpecs  = specSpecs ++ homeSpecs
  let tgtMod    = ModName Target (moduleName (ms_mod modSum))
  return        $ (tgtMod, tgtSpec) : impSpecs

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

checkFilePragmas :: GhcMonadLike m => [Located String] -> m ()
checkFilePragmas = Misc.applyNonNull (return ()) throw . mapMaybe err
  where
    err pragma
      | check (val pragma) = Just (ErrFilePragma $ fSrcSpan pragma :: Error)
      | otherwise          = Nothing
    check pragma           = any (`isPrefixOf` pragma) bad
    bad =
      [ "-i", "--idirs"
      , "-g", "--ghc-option"
      , "--c-files", "--cfiles"
      ]

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
 
--------------------------------------------------------------------------------
-- | Extract Specifications from GHC -------------------------------------------
--------------------------------------------------------------------------------
extractSpecComments :: ApiAnns -> [(SourcePos, String)]
extractSpecComments = mapMaybe extractSpecComment
                    . concat
                    . M.elems
                    . snd


-- | 'extractSpecComment' pulls out the specification part from a full comment
--   string, i.e. if the string is of the form:
--   1. '{-@ S @-}' then it returns the substring 'S',
--   2. '{-@ ... -}' then it throws a malformed SPECIFICATION ERROR, and
--   3. Otherwise it is just treated as a plain comment so we return Nothing.
extractSpecComment :: GHC.Located AnnotationComment -> Maybe (SourcePos, String)

extractSpecComment (GHC.L sp (AnnBlockComment text))
  | isPrefixOf "{-@" text && isSuffixOf "@-}" text          -- valid   specification
  = Just (offsetPos, take (length text - 6) $ drop 3 text)
  | isPrefixOf "{-@" text                                   -- invalid specification
  = uError $ ErrParseAnn sp "A valid specification must have a closing '@-}'."
  where
    offsetPos = incSourceColumn (srcSpanSourcePos sp) 3
extractSpecComment _ = Nothing

extractSpecQuotes :: TypecheckedModule -> [BPspec]
extractSpecQuotes = 
  extractSpecQuotes' (ms_mod . pm_mod_summary . tm_parsed_module) 
                     (tcg_anns . fst . tm_internals_)

extractSpecQuotes' :: (a -> Module) -> (a -> [Annotation]) -> a -> [BPspec]
extractSpecQuotes' thisModule getAnns a = mapMaybe extractSpecQuote anns
  where
    anns = map ann_value $
           filter (isOurModTarget . ann_target) $
           getAnns a

    isOurModTarget (ModuleTarget mod1) = mod1 == thisModule a
    isOurModTarget _ = False

extractSpecQuote :: AnnPayload -> Maybe BPspec
extractSpecQuote payload = 
  case fromSerialized deserializeWithData payload of
    Nothing -> Nothing
    Just qt -> Just $ refreshSymbols $ liquidQuoteSpec qt

refreshSymbols :: Data a => a -> a
refreshSymbols = everywhere (mkT refreshSymbol)

refreshSymbol :: Symbol -> Symbol
refreshSymbol = symbol . symbolText

--------------------------------------------------------------------------------
-- | Finding & Parsing Files ---------------------------------------------------
--------------------------------------------------------------------------------

-- | Handle Spec Files ---------------------------------------------------------

findAndParseSpecFiles :: GhcMonadLike m
                      => Config
                      -> S.HashSet FilePath
                      -> ModSummary
                      -> [Module]
                      -> m [(ModName, Ms.BareSpec)]
findAndParseSpecFiles cfg paths modSummary reachable = do
  modGraph <- GhcMonadLike.getModuleGraph
  impSumms <- mapM GhcMonadLike.getModSummary (moduleName <$> reachable)
  imps''   <- nub . concat <$> mapM modSummaryImports (modSummary : impSumms)
  imps'    <- filterM ((not <$>) . isHomeModule) imps''
  let imps  = m2s <$> imps'
  fs'      <- liftIO $ moduleFiles modGraph Spec paths imps
  -- liftIO  $ whenLoud  $ print ("moduleFiles-imps'': "  ++ show (m2s <$> imps''))
  -- liftIO  $ whenLoud  $ print ("moduleFiles-imps' : "  ++ show (m2s <$> imps'))
  -- liftIO  $ whenLoud  $ print ("moduleFiles-imps  : "  ++ show imps)
  -- liftIO  $ whenLoud  $ print ("moduleFiles-Paths : "  ++ show paths)
  -- liftIO  $ whenLoud  $ print ("moduleFiles-Specs : "  ++ show fs')
  patSpec  <- liftIO $ getPatSpec  modGraph paths $ totalityCheck cfg
  rlSpec   <- liftIO $ getRealSpec modGraph paths $ not (linear cfg)
  let fs    = patSpec ++ rlSpec ++ fs'
  liftIO $ transParseSpecs modGraph paths mempty mempty fs
  where
    m2s = moduleNameString . moduleName

getPatSpec :: ModuleGraph -> S.HashSet FilePath -> Bool -> IO [FilePath]
getPatSpec modGraph paths totalitycheck
 | totalitycheck = moduleFiles modGraph Spec paths [patErrorName]
 | otherwise     = return []
 where
  patErrorName   = "PatErr"

getRealSpec :: ModuleGraph -> S.HashSet FilePath -> Bool -> IO [FilePath]
getRealSpec modGraph paths freal
  | freal     = moduleFiles modGraph Spec paths [realSpecName]
  | otherwise = moduleFiles modGraph Spec paths [notRealSpecName]
  where
    realSpecName    = "Real"
    notRealSpecName = "NotReal"

transParseSpecs :: ModuleGraph
                -> S.HashSet FilePath
                -> S.HashSet FilePath 
                -> [(ModName, Ms.BareSpec)]
                -> [FilePath]
                -> IO [(ModName, Ms.BareSpec)]
transParseSpecs _ _ _ specs [] = return specs
transParseSpecs modGraph paths seenFiles specs newFiles = do
  -- liftIO $ print ("TRANS-PARSE-SPECS", seenFiles, newFiles)
  newSpecs      <- liftIO $ mapM parseSpecFile newFiles
  impFiles      <- moduleFiles modGraph Spec paths $ specsImports newSpecs
  let seenFiles' = seenFiles `S.union` S.fromList newFiles
  let specs'     = specs ++ map (second noTerm) newSpecs
  let newFiles'  = filter (not . (`S.member` seenFiles')) impFiles
  transParseSpecs modGraph paths seenFiles' specs' newFiles'
  where
    specsImports ss = nub $ concatMap (map symbolString . Ms.imports . snd) ss

noTerm :: Ms.BareSpec -> Ms.BareSpec
noTerm spec = spec { Ms.decr = mempty, Ms.lazy = mempty, Ms.termexprs = mempty }

parseSpecFile :: FilePath -> IO (ModName, Ms.BareSpec)
parseSpecFile file = either throw return . specSpecificationP file =<< Misc.sayReadFile file

-- Find Hquals Files -----------------------------------------------------------

-- _moduleHquals :: MGIModGuts
--              -> [FilePath]
--              -> FilePath
--              -> [String]
--              -> [FilePath]
--              -> Ghc [FilePath]
-- _moduleHquals mgi paths target imps incs = do
--   hqs   <- specIncludes Hquals paths incs
--   hqs'  <- moduleFiles Hquals paths (mgi_namestring mgi : imps)
--   hqs'' <- liftIO $ filterM doesFileExist [extFileName Hquals target]
--   return $ Misc.sortNub $ hqs'' ++ hqs ++ hqs'

-- Find Files for Modules ------------------------------------------------------

moduleFiles :: ModuleGraph -> Ext -> S.HashSet FilePath -> [String] -> IO [FilePath]
moduleFiles modGraph ext paths names = catMaybes <$> mapM (moduleFile modGraph ext paths) names

moduleFile :: ModuleGraph -> Ext -> S.HashSet FilePath -> String -> IO (Maybe FilePath)
moduleFile modGraph ext (S.toList -> paths) name
  | ext `elem` [Hs, LHs] = do
    let graph = mgModSummaries modGraph
    case find (\m -> not (isBootSummary m) &&
                     name == moduleNameString (ms_mod_name m)) graph of
      Nothing -> getFileInDirs (extModuleName name ext) paths
      Just ms -> return $ normalise <$> ml_hs_file (ms_location ms)
  | otherwise = getFileInDirs (extModuleName name ext) paths

specIncludes :: Ext -> [FilePath] -> [FilePath] -> Ghc [FilePath]
specIncludes ext paths reqs = do
  let libFile = extFileNameR ext $ symbolString preludeName
  let incFiles = catMaybes $ reqFile ext <$> reqs
  liftIO $ forM (libFile : incFiles) $ \f -> do
    mfile <- getFileInDirs f paths
    case mfile of
      Just file -> return file
      Nothing   -> panic Nothing $ "cannot find " ++ f ++ " in " ++ show paths

reqFile :: Ext -> FilePath -> Maybe FilePath
reqFile ext s
  | isExtFile ext s = Just s
  | otherwise = Nothing

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



--------------------------------------------------------------------------------
-- | Pretty Printing -----------------------------------------------------------
--------------------------------------------------------------------------------

instance PPrint GhcSpec where
  pprintTidy k spec = vcat
    [ "******* Target Variables ********************"
    , pprintTidy k $ gsTgtVars (gsVars spec)
    , "******* Type Signatures *********************"
    , pprintLongList k (gsTySigs (gsSig spec))
    , "******* Assumed Type Signatures *************"
    , pprintLongList k (gsAsmSigs (gsSig spec))
    , "******* DataCon Specifications (Measure) ****"
    , pprintLongList k (gsCtors (gsData spec))
    , "******* Measure Specifications **************"
    , pprintLongList k (gsMeas (gsData spec))       ]

instance PPrint GhcInfo where
  pprintTidy k info = vcat
    [ -- "*************** Imports *********************"
      -- , intersperse comma $ text <$> imports info
      -- , "*************** Includes ********************"
      -- , intersperse comma $ text <$> includes info
      "*************** Imported Variables **********"
    , pprDoc $ giImpVars (giSrc info)
    , "*************** Defined Variables ***********"
    , pprDoc $ giDefVars (giSrc info)
    , "*************** Specification ***************"
    , pprintTidy k $ giSpec info
    , "*************** Core Bindings ***************"
    , pprintCBs $ giCbs (giSrc info)                ]

-- RJ: the silly guards below are to silence the unused-var checker
pprintCBs :: [CoreBind] -> Doc
pprintCBs
  | otherwise = pprintCBsTidy
  | otherwise = pprintCBsVerbose
  where
    pprintCBsTidy    = pprDoc . tidyCBs
    pprintCBsVerbose = text . O.showSDocDebug unsafeGlobalDynFlags . O.ppr . tidyCBs

instance Show GhcInfo where
  show = showpp

instance PPrint TargetVars where
  pprintTidy _ AllVars   = text "All Variables"
  pprintTidy k (Only vs) = text "Only Variables: " <+> pprintTidy k vs

------------------------------------------------------------------------
-- Dealing with Errors ---------------------------------------------------
------------------------------------------------------------------------

instance Result SourceError where
  result = (`Crash` "Invalid Source") . sourceErrors ""
