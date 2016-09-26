{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}

module Language.Haskell.Liquid.GHC.Interface (

  -- * extract all information needed for verification
    getGhcInfo
  , runLiquidGhc

  -- * printer
  , pprintCBs

  -- * predicates
  , isExportedVar
  , exportedVars
  ) where

import Prelude hiding (error)

import qualified Outputable as O
import GHC hiding (Target, desugarModule, Located)
import qualified GHC
import GHC.Paths (libdir)

import Annotations
import Bag
import Class
import CoreMonad
import CoreSyn
import DataCon
import Digraph
import DriverPhases
import DriverPipeline
import DynFlags
import ErrUtils
import Finder
import HscTypes hiding (Target)
import IdInfo
import InstEnv
import Module
import Panic (throwGhcExceptionIO)
import Serialized
import TcRnTypes
import Var
import NameSet

import Control.Exception
import Control.Monad

import Data.Bifunctor
import Data.Data
import Data.List hiding (intersperse)
import Data.Maybe

import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import qualified Data.HashSet as S
import qualified Data.Map as M

import System.Console.CmdArgs.Verbosity hiding (Loud)
import System.Directory
import System.FilePath
import System.IO.Temp

import Text.Parsec.Pos
import Text.PrettyPrint.HughesPJ hiding (first)

import Language.Fixpoint.Types hiding (Error, Result, Expr)
import Language.Fixpoint.Misc

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GHC.Misc
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.PrettyPrint
import Language.Haskell.Liquid.Types.Visitors
import Language.Haskell.Liquid.UX.CmdLine
import Language.Haskell.Liquid.UX.Config (totalityCheck)
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.UX.Tidy
import Language.Fixpoint.Utils.Files

--------------------------------------------------------------------------------
-- | GHC Interface Pipeline ----------------------------------------------------
--------------------------------------------------------------------------------

getGhcInfo :: Maybe HscEnv -> Config -> [FilePath] -> IO ([GhcInfo], HscEnv)
getGhcInfo hscEnv cfg tgtFiles' = do
  tgtFiles <- mapM canonicalizePath tgtFiles'
  _        <- mapM_ createTempDirectoryIfMissing tgtFiles
  logicMap <- liftIO makeLogicMap
  runLiquidGhc hscEnv cfg (getGhcInfo' cfg logicMap tgtFiles)

getGhcInfo' :: Config -> Either Error LogicMap
            -> [FilePath]
            -> Ghc ([GhcInfo], HscEnv)
getGhcInfo' cfg logicMap tgtFiles = do
  _           <- compileCFiles cfg
  homeModules <- configureGhcTargets tgtFiles
  depGraph    <- buildDepGraph homeModules
  ghcInfo     <- processModules cfg logicMap tgtFiles depGraph homeModules
  hscEnv      <- getSession
  return (ghcInfo, hscEnv)

createTempDirectoryIfMissing :: FilePath -> IO ()
createTempDirectoryIfMissing tgtFile = tryIgnore "create temp directory" $
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
      defaultCleanupHandler df act

configureDynFlags :: Config -> FilePath -> Ghc DynFlags
configureDynFlags cfg tmp = do
  df <- getSessionDynFlags
  (df',_,_) <- parseDynamicFlags df $ map noLoc $ ghcOptions cfg
  loud <- liftIO isLoud
  let df'' = df' { importPaths  = nub $ idirs cfg ++ importPaths df'
                 , libraryPaths = nub $ idirs cfg ++ libraryPaths df'
                 , includePaths = nub $ idirs cfg ++ includePaths df'
                 , packageFlags = ExposePackage (PackageArg "ghc-prim")
                                                (ModRenaming True [])
                                : packageFlags df'
                 -- , profAuto     = ProfAutoCalls
                 , ghcLink      = LinkInMemory
                 , hscTarget    = HscInterpreted
                 , ghcMode      = CompManager
                 -- prevent GHC from printing anything, unless in Loud mode
                 , log_action   = if loud
                                    then defaultLogAction
                                    else \_ _ _ _ _ -> return ()
                 -- redirect .hi/.o/etc files to temp directory
                 , objectDir    = Just tmp
                 , hiDir        = Just tmp
                 , stubDir      = Just tmp
                 } `xopt_set` Opt_MagicHash
                   `xopt_set` Opt_DeriveGeneric
                   `xopt_set` Opt_StandaloneDeriving
                   `gopt_set` Opt_ImplicitImportQualified
                   `gopt_set` Opt_PIC
  _ <- setSessionDynFlags df''
  return df''

configureGhcTargets :: [FilePath] -> Ghc ModuleGraph
configureGhcTargets tgtFiles = do
  targets         <- mapM (`guessTarget` Nothing) tgtFiles
  _               <- setTargets targets
  moduleGraph     <- depanal [] False
  let homeModules  = flattenSCCs $ topSortModuleGraph False moduleGraph Nothing
  _               <- setTargetModules $ moduleName . ms_mod <$> homeModules
  return homeModules

setTargetModules :: [ModuleName] -> Ghc ()
setTargetModules modNames = setTargets $ mkTarget <$> modNames
  where
    mkTarget modName = GHC.Target (TargetModule modName) True Nothing

compileCFiles :: Config -> Ghc ()
compileCFiles cfg = do
  df  <- getSessionDynFlags
  _   <- setSessionDynFlags $
           df { includePaths = nub $ idirs cfg ++ includePaths df
              , importPaths  = nub $ idirs cfg ++ importPaths df
              , libraryPaths = nub $ idirs cfg ++ libraryPaths df }
  hsc <- getSession
  os  <- mapM (\x -> liftIO $ compileFile hsc StopLn (x,Nothing)) (nub $ cFiles cfg)
  df  <- getSessionDynFlags
  void $ setSessionDynFlags $ df { ldInputs = nub $ map (FileOption "") os ++ ldInputs df }

--------------------------------------------------------------------------------
-- Home Module Dependency Graph ------------------------------------------------
--------------------------------------------------------------------------------

type DepGraph = Graph DepGraphNode
type DepGraphNode = Node Module ()

reachableModules :: DepGraph -> Module -> [Module]
reachableModules depGraph mod =
  snd3 <$> tail (reachableG depGraph ((), mod, []))

buildDepGraph :: ModuleGraph -> Ghc DepGraph
buildDepGraph homeModules =
  graphFromEdgedVertices <$> mapM mkDepGraphNode homeModules

mkDepGraphNode :: ModSummary -> Ghc DepGraphNode
mkDepGraphNode modSummary = ((), ms_mod modSummary, ) <$>
  (filterM isHomeModule =<< modSummaryImports modSummary)

isHomeModule :: Module -> Ghc Bool
isHomeModule mod = do
  homePkg <- thisPackage <$> getSessionDynFlags
  return $ modulePackageKey mod == homePkg

modSummaryImports :: ModSummary -> Ghc [Module]
modSummaryImports modSummary =
  mapM (importDeclModule (ms_mod modSummary) . unLoc)
       (ms_textual_imps modSummary)

importDeclModule :: Module -> ImportDecl a -> Ghc Module
importDeclModule fromMod decl = do
  hscEnv <- getSession
  let modName = unLoc $ ideclName decl
  let pkgQual = ideclPkgQual decl
  result <- liftIO $ findImportedModule hscEnv modName pkgQual
  case result of
    Finder.Found _ mod -> return mod
    _ -> do
      dflags <- getSessionDynFlags
      liftIO $ throwGhcExceptionIO $ ProgramError $
        O.showPpr dflags (moduleName fromMod) ++ ": " ++
        O.showSDoc dflags (cannotFindModule dflags modName result)

--------------------------------------------------------------------------------
-- | Extract Ids ---------------------------------------------------------------
--------------------------------------------------------------------------------

exportedVars :: GhcInfo -> [Var]
exportedVars info = filter (isExportedVar info) (defVars info)

isExportedVar :: GhcInfo -> Var -> Bool
isExportedVar info v = n `elemNameSet` ns
  where
    n                = getName v
    ns               = gsExports (spec info)


classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: CoreProgram -> Maybe [DFunId] -> [Id]
derivedVars cbs (Just fds) = concatMap (derivedVs cbs) fds
derivedVars _   Nothing    = []

derivedVs :: CoreProgram -> DFunId -> [Id]
derivedVs cbs fd   = concatMap bindersOf cbs' ++ deps
  where
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

definedVars :: CoreProgram -> [Id]
definedVars = concatMap defs
  where
    defs (NonRec x _) = [x]
    defs (Rec xes)    = map fst xes

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

type SpecEnv = ModuleEnv (ModName, Ms.BareSpec)

processModules :: Config -> Either Error LogicMap -> [FilePath] -> DepGraph
               -> ModuleGraph
               -> Ghc [GhcInfo]
processModules cfg logicMap tgtFiles depGraph homeModules =
  catMaybes . snd <$> mapAccumM go emptyModuleEnv homeModules
  where
    go = processModule cfg logicMap (S.fromList tgtFiles) depGraph

processModule :: Config -> Either Error LogicMap -> S.HashSet FilePath -> DepGraph
              -> SpecEnv -> ModSummary
              -> Ghc (SpecEnv, Maybe GhcInfo)
processModule cfg logicMap tgtFiles depGraph specEnv modSummary = do
  let mod              = ms_mod modSummary
  _                   <- liftIO $ whenLoud $ putStrLn $ "Module: " ++ showPpr (moduleName mod)
  file                <- liftIO $ canonicalizePath $ modSummaryHsFile modSummary
  _                   <- loadDependenciesOf $ moduleName mod
  parsed              <- parseModule $ keepRawTokenStream modSummary
  let specComments     = extractSpecComments parsed
  typechecked         <- typecheckModule $ ignoreInline parsed
  let specQuotes       = extractSpecQuotes typechecked
  _                   <- loadModule' typechecked
  (modName, bareSpec) <- either throw return $ hsSpecificationP (moduleName mod) specComments specQuotes
  _                   <- checkFilePragmas $ Ms.pragmas bareSpec
  let specEnv'         = extendModuleEnv specEnv mod (modName, noTerm bareSpec)
  (specEnv', ) <$> if not (file `S.member` tgtFiles)
    then return Nothing
    else Just <$> processTargetModule cfg logicMap depGraph specEnv file typechecked bareSpec

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

processTargetModule :: Config -> Either Error LogicMap -> DepGraph
                    -> SpecEnv
                    -> FilePath -> TypecheckedModule -> Ms.BareSpec
                    -> Ghc GhcInfo
processTargetModule cfg0 logicMap depGraph specEnv file typechecked bareSpec = do
  cfg               <- liftIO $ withPragmas cfg0 file $ Ms.pragmas bareSpec
  let modSummary     = pm_mod_summary $ tm_parsed_module typechecked
  let mod            = ms_mod modSummary
  let modName        = ModName Target $ moduleName mod
  desugared         <- desugarModule typechecked
  let modGuts        = makeMGIModGuts desugared
  hscEnv            <- getSession
  coreBinds         <- liftIO $ anormalize cfg hscEnv modGuts
  _                 <- liftIO $ whenNormal $ donePhase Loud "A-Normalization"
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs modGuts)
  let impVs          = importVars coreBinds ++ classCons (mgi_cls_inst modGuts)
  let defVs          = definedVars coreBinds
  let useVs          = readVars coreBinds
  let letVs          = letVars coreBinds
  let derVs          = derivedVars coreBinds $ ((is_dfun <$>) <$>) $ mgi_cls_inst modGuts
  let paths          = nub $ idirs cfg ++ importPaths (ms_hspp_opts modSummary)
  _                 <- liftIO $ whenLoud $ putStrLn $ "paths = " ++ show paths
  let reachable      = reachableModules depGraph mod
  specSpecs         <- findAndParseSpecFiles cfg paths modSummary reachable
  let homeSpecs      = getCachedBareSpecs specEnv reachable
  let impSpecs       = specSpecs ++ homeSpecs
  (spc, imps, incs) <- toGhcSpec cfg coreBinds (impVs ++ defVs) letVs modName modGuts bareSpec logicMap impSpecs
  _                 <- liftIO $ whenLoud $ putStrLn $ "Module Imports: " ++ show imps
  hqualsFiles       <- moduleHquals modGuts paths file imps incs
  return GI { target    = file
            , targetMod = moduleName mod
            , env       = hscEnv
            , cbs       = coreBinds
            , derVars   = derVs
            , impVars   = impVs
            , defVars   = letVs ++ dataCons
            , useVars   = useVs
            , hqFiles   = hqualsFiles
            , imports   = imps
            , includes  = incs
            , spec      = spc                }

toGhcSpec :: GhcMonad m
          => Config
          -> [CoreBind]
          -> [Var]
          -> [Var]
          -> ModName
          -> MGIModGuts
          -> Ms.Spec (Located BareType) LocSymbol
          -> Either Error LogicMap
          -> [(ModName, Ms.BareSpec)]
          -> m (GhcSpec, [String], [FilePath])
toGhcSpec cfg cbs vars letVs tgtMod mgi tgtSpec lm impSpecs = do
  let tgtCxt    = IIModule $ getModName tgtMod
  let impCxt    = map (IIDecl . qualImportDecl . getModName . fst) impSpecs
  _            <- setContext (tgtCxt : impCxt)
  hsc          <- getSession
  let impNames  = map (getModString . fst) impSpecs
  let exports   = mgi_exports mgi
  let specs     = (tgtMod, tgtSpec) : impSpecs
  let imps      = sortNub $ impNames ++ [ symbolString x | (_, sp) <- specs, x <- Ms.imports sp ]
  ghcSpec      <- liftIO $ makeGhcSpec cfg tgtMod cbs (mgi_cls_inst mgi) vars letVs exports hsc lm specs
  return (ghcSpec, imps, Ms.includes tgtSpec)

modSummaryHsFile :: ModSummary -> FilePath
modSummaryHsFile modSummary =
  fromMaybe
    (panic Nothing $
      "modSummaryHsFile: missing .hs file for " ++
      showPpr (ms_mod modSummary))
    (ml_hs_file $ ms_location modSummary)

getCachedBareSpecs :: SpecEnv -> [Module] -> [(ModName, Ms.BareSpec)]
getCachedBareSpecs specEnv mods = lookupBareSpec <$> mods
  where
    lookupBareSpec mod =
      fromMaybe
        (impossible Nothing $
           "lookupBareSpec: missing module " ++ showPpr mod)
        (lookupModuleEnv specEnv mod)

checkFilePragmas :: [Located String] -> Ghc ()
checkFilePragmas = applyNonNull (return ()) throw . mapMaybe err
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
-- | Extract Specifications from GHC -------------------------------------------
--------------------------------------------------------------------------------

extractSpecComments :: ParsedModule -> [(SourcePos, String)]
extractSpecComments parsed = mapMaybe extractSpecComment comments
  where
    comments = concat $ M.elems $ snd $ pm_annotations parsed

extractSpecComment :: GHC.Located AnnotationComment -> Maybe (SourcePos, String)
extractSpecComment (GHC.L span (AnnBlockComment text))
  | length text > 2 && isPrefixOf "{-@" text && isSuffixOf "@-}" text =
    Just (offsetPos, take (length text - 6) $ drop 3 text)
  where
    offsetPos = incSourceColumn (srcSpanSourcePos span) 3
extractSpecComment _ = Nothing

extractSpecQuotes :: TypecheckedModule -> [BPspec]
extractSpecQuotes typechecked = mapMaybe extractSpecQuote anns
  where
    anns = map ann_value $
           filter (isOurModTarget . ann_target) $
           tcg_anns $ fst $ tm_internals_ typechecked

    isOurModTarget (ModuleTarget mod1) = mod1 == mod
    isOurModTarget _ = False

    mod = ms_mod $ pm_mod_summary $ tm_parsed_module typechecked

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

-- Handle Spec Files -----------------------------------------------------------

findAndParseSpecFiles :: Config
                      -> [FilePath]
                      -> ModSummary
                      -> [Module]
                      -> Ghc [(ModName, Ms.BareSpec)]
findAndParseSpecFiles cfg paths modSummary reachable = do
  impSumms <- mapM getModSummary (moduleName <$> reachable)
  imps''   <- nub . concat <$> mapM modSummaryImports (modSummary : impSumms)
  imps'    <- filterM ((not <$>) . isHomeModule) imps''
  let imps  = m2s <$> imps'
  fs'      <- moduleFiles Spec paths imps
  -- liftIO    $ print ("moduleFiles-imps'\n"  ++ show (m2s <$> imps'))
  -- liftIO    $ print ("moduleFiles-imps\n"   ++ show imps)
  -- liftIO    $ print ("moduleFiles-Paths\n"  ++ show paths)
  -- liftIO    $ print ("moduleFiles-Specs\n"  ++ show fs')
  patSpec  <- getPatSpec paths $ totalityCheck cfg
  rlSpec   <- getRealSpec paths $ not $ linear cfg
  let fs    = patSpec ++ rlSpec ++ fs'
  transParseSpecs paths mempty mempty fs
  where
    m2s = moduleNameString . moduleName

getPatSpec :: [FilePath] -> Bool -> Ghc [FilePath]
getPatSpec paths totalitycheck
 | totalitycheck = moduleFiles Spec paths [patErrorName]
 | otherwise     = return []
 where
  patErrorName = "PatErr"

getRealSpec :: [FilePath] -> Bool -> Ghc [FilePath]
getRealSpec paths freal
  | freal     = moduleFiles Spec paths [realSpecName]
  | otherwise = moduleFiles Spec paths [notRealSpecName]
  where
    realSpecName    = "Real"
    notRealSpecName = "NotReal"

transParseSpecs :: [FilePath]
                -> S.HashSet FilePath -> [(ModName, Ms.BareSpec)]
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
parseSpecFile file = either throw return . specSpecificationP file =<< readFile file

-- Find Hquals Files -----------------------------------------------------------

moduleHquals :: MGIModGuts
             -> [FilePath]
             -> FilePath
             -> [String]
             -> [FilePath]
             -> Ghc [FilePath]
moduleHquals mgi paths target imps incs = do
  hqs   <- specIncludes Hquals paths incs
  hqs'  <- moduleFiles Hquals paths (mgi_namestring mgi : imps)
  hqs'' <- liftIO $ filterM doesFileExist [extFileName Hquals target]
  return $ sortNub $ hqs'' ++ hqs ++ hqs'

-- Find Files for Modules ------------------------------------------------------

moduleFiles :: Ext -> [FilePath] -> [String] -> Ghc [FilePath]
moduleFiles ext paths names = catMaybes <$> mapM (moduleFile ext paths) names

moduleFile :: Ext -> [FilePath] -> String -> Ghc (Maybe FilePath)
moduleFile ext paths name
  | ext `elem` [Hs, LHs] = do
    graph <- getModuleGraph
    case find (\m -> not (isBootSummary m) &&
                     name == moduleNameString (ms_mod_name m)) graph of
      Nothing -> liftIO $ getFileInDirs (extModuleName name ext) paths
      Just ms -> return $ normalise <$> ml_hs_file (ms_location ms)
  | otherwise = liftIO $ getFileInDirs (extModuleName name ext) paths

specIncludes :: Ext -> [FilePath] -> [FilePath] -> Ghc [FilePath]
specIncludes ext paths reqs = do
  let libFile = extFileNameR ext $ symbolString preludeName
  let incFiles = catMaybes $ reqFile ext <$> reqs
  liftIO $ forM (libFile : incFiles) $ \f -> do
    mfile <- getFileInDirs f paths
    case mfile of
      Just file -> return file
      Nothing -> panic Nothing $ "cannot find " ++ f ++ " in " ++ show paths

reqFile :: Ext -> FilePath -> Maybe FilePath
reqFile ext s
  | isExtFile ext s = Just s
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Assemble Information for Spec Extraction ------------------------------------
--------------------------------------------------------------------------------

makeMGIModGuts :: DesugaredModule -> MGIModGuts
makeMGIModGuts desugared = miModGuts deriv modGuts
  where
    modGuts = coreModule desugared
    deriv = Just $ instEnvElts $ mg_inst_env modGuts

makeLogicMap :: IO (Either Error LogicMap)
makeLogicMap = do
  lg    <- getCoreToLogicPath
  lspec <- readFile lg
  return $ parseSymbolToLogic lg lspec

--------------------------------------------------------------------------------
-- | Pretty Printing -----------------------------------------------------------
--------------------------------------------------------------------------------

instance PPrint GhcSpec where
  pprintTidy k spec = vcat
    [ "******* Target Variables ********************"
    , pprintTidy k $ gsTgtVars spec
    , "******* Type Signatures *********************"
    , pprintLongList k (gsTySigs spec)
    , "******* Assumed Type Signatures *************"
    , pprintLongList k (gsAsmSigs spec)
    , "******* DataCon Specifications (Measure) ****"
    , pprintLongList k (gsCtors spec)
    , "******* Measure Specifications **************"
    , pprintLongList k (gsMeas spec)                   ]

instance PPrint GhcInfo where
  pprintTidy k info = vcat
    [ "*************** Imports *********************"
    , intersperse comma $ text <$> imports info
    , "*************** Includes ********************"
    , intersperse comma $ text <$> includes info
    , "*************** Imported Variables **********"
    , pprDoc $ impVars info
    , "*************** Defined Variables ***********"
    , pprDoc $ defVars info
    , "*************** Specification ***************"
    , pprintTidy k $ spec info
    , "*************** Core Bindings ***************"
    , pprintCBs $ cbs info                          ]

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
  result = (`Crash` "Invalid Source")
         . concatMap errMsgErrors
         . bagToList
         . srcErrorMessages

errMsgErrors :: ErrMsg -> [TError t]
errMsgErrors e = [ ErrGhc (errMsgSpan e) (pprint e)]
