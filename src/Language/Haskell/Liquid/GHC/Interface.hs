{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE OverloadedStrings         #-}

module Language.Haskell.Liquid.GHC.Interface (

  -- * extract all information needed for verification
    getGhcInfo

  -- * printer
  , pprintCBs
  ) where

import Prelude hiding (error)

import GHC hiding (Target, desugarModule)
-- HEAD
-- import DriverPhases (Phase(..))
-- import DriverPipeline (compileFile)
-- import Text.PrettyPrint.HughesPJ
-- import HscTypes hiding (Target)
-- import CoreSyn
-- import qualified Outputable as O
-- develop
import GHC.Paths (libdir)

import Bag
import Class
import CoreMonad
import CoreSyn
import DataCon
import DriverPhases
import DriverPipeline
import DynFlags
import ErrUtils
import HscTypes hiding (Target)
import IdInfo
import InstEnv
import Var

import Control.Exception
import Control.Monad

import Data.List hiding (intersperse)
import Data.Maybe
import qualified Data.HashSet as S

import System.Console.CmdArgs.Verbosity hiding (Loud)
import System.Directory
import System.FilePath
import System.IO.Temp

import Text.PrettyPrint.HughesPJ

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
import Language.Haskell.Liquid.UX.Tidy
import Language.Fixpoint.Utils.Files

--------------------------------------------------------------------------------
-- GHC Interface Pipeline ------------------------------------------------------
--------------------------------------------------------------------------------

getGhcInfo :: Maybe HscEnv -> Config -> FilePath -> IO (GhcInfo, HscEnv)
getGhcInfo hscEnv cfg0 target = do
  tryIgnore "create temp directory" $
    createDirectoryIfMissing False $ tempDirectory target
  (cfg, name, tgtSpec) <- parseRootTarget cfg0 target
  runLiquidGhc hscEnv cfg $ getGhcInfo' cfg target name tgtSpec

getGhcInfo' :: Config -> FilePath -> ModName -> Ms.BareSpec -> Ghc (GhcInfo, HscEnv)
getGhcInfo' cfg target name tgtSpec = do
  paths <- importPaths <$> getSessionDynFlags
  liftIO $ whenLoud $ putStrLn $ "paths = " ++ show paths

  impSpecs <- findAndLoadTargets cfg paths target

  modGuts <- makeMGIModGuts target
  hscEnv <- getSession
  coreBinds <- liftIO $ anormalize (not $ nocaseexpand cfg) hscEnv modGuts

  logicMap <- liftIO makeLogicMap

  let dataCons = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs modGuts)

  let impVs = importVars coreBinds ++ classCons (mgi_cls_inst modGuts)
  let defVs = definedVars coreBinds
  let useVs = readVars coreBinds
  let letVs = letVars coreBinds
  let derVs = derivedVars coreBinds $ ((is_dfun <$>) <$>) $ mgi_cls_inst modGuts

  (spc, imps, incs) <- moduleSpec cfg coreBinds (impVs ++ defVs) letVs name modGuts tgtSpec logicMap impSpecs
  liftIO $ whenLoud $ putStrLn $ "Module Imports: " ++ show imps
  hqualFiles <- moduleHquals modGuts paths target imps incs

  let info = GI target hscEnv coreBinds derVs impVs (letVs ++ dataCons) useVs hqualFiles imps incs spc
  hscEnv' <- getSession
  return (info, hscEnv')

--------------------------------------------------------------------------------
-- Configure GHC for Liquid Haskell --------------------------------------------
--------------------------------------------------------------------------------

runLiquidGhc :: Maybe HscEnv -> Config -> Ghc a -> IO a
runLiquidGhc hscEnv cfg act =
  withSystemTempDirectory "liquid" $ \tmp ->
    runGhc (Just libdir) $ do
      maybe (return ()) setSession hscEnv
      df <- getSessionDynFlags
      (df',_,_) <- parseDynamicFlags df (map noLoc $ ghcOptions cfg)
      loud <- liftIO isLoud
      let df'' = df' { importPaths  = nub $ idirs cfg ++ importPaths df'
                     , libraryPaths = nub $ idirs cfg ++ libraryPaths df'
                     , includePaths = nub $ idirs cfg ++ includePaths df'
                     , packageFlags = ExposePackage (PackageArg "ghc-prim") (ModRenaming True []) : packageFlags df'
                     -- , profAuto     = ProfAutoCalls
                     , ghcLink      = LinkInMemory
                     --FIXME: this *should* be HscNothing, but that prevents us from
                     -- looking up *unexported* names in another source module..
                     , hscTarget    = HscInterpreted -- HscNothing
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
                       `gopt_set` Opt_ImplicitImportQualified
                       `gopt_set` Opt_PIC
      setSessionDynFlags df''
      defaultCleanupHandler df'' act

--------------------------------------------------------------------------------
-- Parse, Find, & Load Targets -------------------------------------------------
--------------------------------------------------------------------------------

parseRootTarget :: Config -> FilePath -> IO (Config, ModName, Ms.BareSpec)
parseRootTarget cfg0 target = do
  (name, tgtSpec) <- parseSpec target
  cfg <- withPragmas cfg0 target $ Ms.pragmas tgtSpec
  return (cfg, ModName Target $ getModName name, tgtSpec)

findAndLoadTargets :: Config -> [FilePath] -> FilePath -> Ghc [(ModName, Ms.BareSpec)]
findAndLoadTargets cfg paths target = do
  setTargets . return =<< guessTarget target Nothing

  impNames <- allDepNames <$> depanal [] False
  impSpecs <- getSpecs cfg paths target impNames [Spec, Hs, LHs]
  liftIO $ whenNormal $ donePhase Loud "Parsed All Specifications"

  compileCFiles =<< liftIO (foldM (\c (f,_,s) -> withPragmas c f (Ms.pragmas s)) cfg impSpecs)

  impSpecs' <- forM impSpecs $ \(f, n, s) -> do
                 unless (isSpecImport n) $
                   addTarget =<< guessTarget f Nothing
                 return (n, s)
  load LoadAllTargets
  liftIO $ whenNormal $ donePhase Loud "Loaded Targets"

  return impSpecs'

allDepNames :: [ModSummary] -> [String]
allDepNames = concatMap (map declNameString . ms_textual_imps)

declNameString :: GHC.Located (ImportDecl RdrName) -> String
declNameString = moduleNameString . unLoc . ideclName . unLoc

compileCFiles :: Config -> Ghc ()
compileCFiles cfg = do
  df  <- getSessionDynFlags
  setSessionDynFlags $ df { includePaths = nub $ idirs cfg ++ includePaths df
                          , importPaths  = nub $ idirs cfg ++ importPaths df
                          , libraryPaths = nub $ idirs cfg ++ libraryPaths df }
  hsc <- getSession
  os  <- mapM (\x -> liftIO $ compileFile hsc StopLn (x,Nothing)) (nub $ cFiles cfg)
  df  <- getSessionDynFlags
  void $ setSessionDynFlags $ df { ldInputs = map (FileOption "") os ++ ldInputs df }

--------------------------------------------------------------------------------
-- Assemble Information for Spec Extraction ------------------------------------
--------------------------------------------------------------------------------

makeMGIModGuts :: FilePath -> Ghc MGIModGuts
makeMGIModGuts f = do
  modGraph <- getModuleGraph
  case find (\m -> not (isBootSummary m) && f == msHsFilePath m) modGraph of
    Just modSummary -> do
      parsed <- parseModule modSummary
      modGuts <- coreModule <$> (desugarModule =<< typecheckModule (ignoreInline parsed))
      let deriv = Just $ instEnvElts $ mg_inst_env modGuts
      return $! miModGuts deriv modGuts
    Nothing ->
      panic Nothing $ "Ghc Interface: Unable to get GhcModGuts"

makeLogicMap :: IO (Either Error LogicMap)
makeLogicMap = do
  lg    <- getCoreToLogicPath
  lspec <- readFile lg
  return $ parseSymbolToLogic lg lspec

--------------------------------------------------------------------------------
-- Extract Ids -----------------------------------------------------------------
--------------------------------------------------------------------------------

classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: CoreProgram -> Maybe [DFunId] -> [Id]
derivedVars cbs (Just fds) = concatMap (derivedVs cbs) fds
derivedVars _   Nothing    = []

derivedVs :: CoreProgram -> DFunId -> [Id]
derivedVs cbs fd = concatMap bindersOf cbs' ++ deps
  where
    cbs'           = filter f cbs
    f (NonRec x _) = eqFd x
    f (Rec xes)    = any eqFd (fst <$> xes)
    eqFd x         = varName x == varName fd
    deps           = concatMap unfoldDep unfolds
    unfolds        = unfoldingInfo . idInfo <$> concatMap bindersOf cbs'

unfoldDep :: Unfolding -> [Id]
unfoldDep (DFunUnfolding _ _ e)         = concatMap exprDep e
unfoldDep (CoreUnfolding {uf_tmpl = e}) = exprDep e
unfoldDep _                             = []

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
-- Find & Parse Specs ----------------------------------------------------------
--------------------------------------------------------------------------------

getSpecs cfg paths target names exts = do
  fs' <- sortNub <$> moduleImports exts paths names
  patSpec <- getPatSpec paths $ totality cfg
  rlSpec <- getRealSpec paths $ not $ linear cfg
  let fs = patSpec ++ rlSpec ++ fs'
  transParseSpecs exts paths (S.singleton target) mempty (map snd fs \\ [target])

getPatSpec paths totalitycheck
 | totalitycheck = (map (patErrorName,)) . maybeToList <$> moduleFile paths patErrorName Spec
 | otherwise     = return []
 where
  patErrorName = "PatErr"

getRealSpec paths freal
  | freal     = (map (realSpecName,))    . maybeToList <$> moduleFile paths realSpecName    Spec
  | otherwise = (map (notRealSpecName,)) . maybeToList <$> moduleFile paths notRealSpecName Spec
  where
    realSpecName    = "Real"
    notRealSpecName = "NotReal"


transParseSpecs _ _ _ specs [] = return specs
transParseSpecs exts paths seenFiles specs newFiles = do
  newSpecs <- liftIO $ mapM (\f -> addFst3 f <$> parseSpec f) newFiles
  impFiles <- moduleImports exts paths $ specsImports newSpecs
  let seenFiles' = seenFiles `S.union` (S.fromList newFiles)
  let specs'     = specs ++ map (third3 noTerm) newSpecs
  let newFiles'  = [f | (_, f) <- impFiles, not (f `S.member` seenFiles')]
  transParseSpecs exts paths seenFiles' specs' newFiles'
  where
    specsImports ss = nub $ concatMap (map symbolString . Ms.imports . thd3) ss
    noTerm spec = spec { Ms.decr = mempty, Ms.lazy = mempty, Ms.termexprs = mempty }

parseSpec :: FilePath -> IO (ModName, Ms.BareSpec)
parseSpec file = either throw return . specParser file =<< readFile file

specParser f str
  | isExtFile Spec   f = specSpecificationP f str
  | isExtFile Hs     f = hsSpecificationP   f str
  | isExtFile HsBoot f = hsSpecificationP   f str
  | isExtFile LHs    f = lhsSpecificationP  f str
  | otherwise          = panic Nothing $ "SpecParser: Cannot Parse File " ++ f


moduleSpec cfg cbs vars letVs tgtMod mgi tgtSpec lm impSpecs = do
  let tgtCxt = IIModule $ getModName tgtMod
  let impCxt = map (IIDecl . qualImportDecl . getModName . fst) impSpecs
  setContext (tgtCxt : impCxt)

  hsc <-getSession

  let impNames = map (getModString . fst) impSpecs
  let exports  = mgi_exports mgi

  let specs = (tgtMod, tgtSpec) : impSpecs
  let imps  = sortNub $ impNames ++ [ symbolString x
                                    | (_, sp) <- specs
                                    , x <- Ms.imports sp
                                    ]

  ghcSpec <- liftIO $ makeGhcSpec cfg tgtMod cbs vars letVs exports hsc lm specs
  return (ghcSpec, imps, Ms.includes tgtSpec)

moduleHquals mgi paths target imps incs = do
  hqs   <- specIncludes Hquals paths incs
  hqs'  <- moduleImports [Hquals] paths (mgi_namestring mgi : imps)
  hqs'' <- liftIO $ filterM doesFileExist [extFileName Hquals target]
  return $ sortNub $ hqs'' ++ hqs ++ (snd <$> hqs')


moduleImports :: [Ext] -> [FilePath] -> [String] -> Ghc [(String, FilePath)]
moduleImports exts paths names = liftM concat $ forM names $ \name ->
  map (name,) . catMaybes <$> mapM (moduleFile paths name) exts

moduleFile :: [FilePath] -> String -> Ext -> Ghc (Maybe FilePath)
moduleFile paths name ext
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
-- Pretty Printing -------------------------------------------------------------
--------------------------------------------------------------------------------

instance PPrint GhcSpec where
  pprintTidy k spec = vcat
    [ "******* Target Variables ********************"
    , pprintTidy k $ tgtVars spec
    , "******* Type Signatures *********************"
    , pprintLongList k (tySigs spec)
    , "******* Assumed Type Signatures *************"
    , pprintLongList k (asmSigs spec)
    , "******* DataCon Specifications (Measure) ****"
    , pprintLongList k (ctors spec)
    , "******* Measure Specifications **************"
    , pprintLongList k (meas spec)                   ]

instance PPrint GhcInfo where
  pprintTidy _ info = vcat
    [ "*************** Imports *********************"
    , intersperse comma $ text <$> imports info
    , "*************** Includes ********************"
    , intersperse comma $ text <$> includes info
    , "*************** Imported Variables **********"
    , pprDoc $ impVars info
    , "*************** Defined Variables ***********"
    , pprDoc $ defVars info
    , "*************** Specification ***************"
    , pprint $ spec info
    , "*************** Core Bindings ***************"
    , pprintCBs $ cbs info                          ]


pprintCBs :: [CoreBind] -> Doc
pprintCBs
  | True      = pprintCBsTidy
  | otherwise = pprintCBsVerbose

pprintCBsTidy    = pprDoc . tidyCBs
pprintCBsVerbose = text . O.showSDocDebug unsafeGlobalDynFlags . O.ppr . tidyCBs

-- pprintCBs = showSDocDebug . tidyCBs
-- showSDoc sdoc = Out.renderWithStyle unsafeGlobalDynFlags sdoc (Out.mkUserStyle Out.alwaysQualify Out.AllTheWay)
-- showSDocDump  = Out.showSDocDump unsafeGlobalDynFlags


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

errMsgErrors e = [ ErrGhc (errMsgSpan e) (pprint e)]
