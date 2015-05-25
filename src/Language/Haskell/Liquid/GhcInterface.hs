{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Haskell.Liquid.GhcInterface (

  -- * extract all information needed for verification
    getGhcInfo

  ) where
import IdInfo
import InstEnv
import Bag (bagToList)
import ErrUtils
import GHC hiding (Target, desugarModule)
import DriverPhases (Phase(..))
import DriverPipeline (compileFile)
import Text.PrettyPrint.HughesPJ
import HscTypes hiding (Target)
import CoreSyn

import Class
import Var
import CoreMonad    (liftIO)
import DataCon
import qualified Control.Exception as Ex

import GHC.Paths (libdir)
import System.FilePath ( replaceExtension, normalise)

import DynFlags
import Control.Monad (filterM, foldM, when, forM, forM_, liftM)
import Control.Applicative  hiding (empty)
import Data.Monoid hiding ((<>))
import Data.List (find, nub)
import Data.Maybe (catMaybes, maybeToList)
import qualified Data.HashSet        as S

import System.Console.CmdArgs.Verbosity (whenLoud)
import System.Directory (removeFile, createDirectory, doesFileExist)
import Language.Fixpoint.Types hiding (Result, Expr)
import Language.Fixpoint.Misc

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.ANFTransform
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.PrettyPrint

import Language.Haskell.Liquid.Visitors

import Language.Haskell.Liquid.CmdLine (withPragmas)
import Language.Haskell.Liquid.Parse

import Language.Fixpoint.Names
import Language.Fixpoint.Files

import qualified Language.Haskell.Liquid.Measure as Ms


--------------------------------------------------------------------
getGhcInfo :: Config -> FilePath -> IO (Either ErrorResult GhcInfo)
--------------------------------------------------------------------
getGhcInfo cfg target = (Right <$> getGhcInfo' cfg target)
                          `Ex.catch` (\(e :: SourceError) -> handle e)
                          `Ex.catch` (\(e :: Error)       -> handle e)
                          `Ex.catch` (\(e :: [Error])     -> handle e)
  where
    handle            = return . Left . result


getGhcInfo' cfg0 target
  = runGhc (Just libdir) $ do
      liftIO              $ cleanFiles target
      addTarget         =<< guessTarget target Nothing
      (name,tgtSpec)     <- liftIO $ parseSpec target
      cfg                <- liftIO $ withPragmas cfg0 target $ Ms.pragmas tgtSpec
      let paths           = idirs cfg
      updateDynFlags cfg
      liftIO              $ whenLoud $ putStrLn ("paths = " ++ show paths)
      let name'           = ModName Target (getModName name)
      impNames           <- allDepNames <$> depanal [] False
      impSpecs           <- getSpecs (real cfg) (totality cfg) target paths impNames [Spec, Hs, LHs]
      compileCFiles      =<< liftIO (foldM (\c (f,_,s) -> withPragmas c f (Ms.pragmas s)) cfg impSpecs)
      impSpecs'          <- forM impSpecs $ \(f,n,s) -> do
        when (not $ isSpecImport n) $
          addTarget =<< guessTarget f Nothing
        return (n,s)
      load LoadAllTargets
      modguts            <- getGhcModGuts1 target
      hscEnv             <- getSession
      coreBinds          <- liftIO $ anormalize (not $ nocaseexpand cfg) hscEnv modguts
      let datacons        = [ dataConWorkId dc
                            | tc <- mgi_tcs modguts
                            , dc <- tyConDataCons tc
                            ]
      let impVs           = importVars  coreBinds ++ classCons (mgi_cls_inst modguts)
      let defVs           = definedVars coreBinds
      let useVs           = readVars    coreBinds
      let letVs           = letVars     coreBinds
      let derVs           = derivedVars coreBinds $ fmap (fmap is_dfun) $ mgi_cls_inst modguts
      logicmap           <- liftIO makeLogicMap
      (spec, imps, incs) <- moduleSpec cfg coreBinds (impVs ++ defVs) letVs name' modguts tgtSpec logicmap impSpecs'
      liftIO              $ whenLoud $ putStrLn $ "Module Imports: " ++ show imps
      hqualFiles         <- moduleHquals modguts paths target imps incs
      return              $ GI hscEnv coreBinds derVs impVs (letVs ++ datacons) useVs hqualFiles imps incs spec


makeLogicMap
  = do lg    <- getCoreToLogicPath
       lspec <- readFile lg
       return $ parseSymbolToLogic lg lspec

classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: CoreProgram -> Maybe [DFunId] -> [Id]
derivedVars cbs (Just fds) = concatMap (derivedVs cbs) fds
derivedVars _    Nothing    = []

derivedVs :: CoreProgram -> DFunId -> [Id]
derivedVs cbs fd = concatMap bindersOf cbf ++ deps
  where cbf            = filter f cbs

        f (NonRec x _) = eqFd x
        f (Rec xes   ) = any eqFd (fst <$> xes)
        eqFd x         = varName x == varName fd
        deps :: [Id]
        deps = concatMap dep $ (unfoldingInfo . idInfo <$> concatMap bindersOf cbf)

        dep (DFunUnfolding _ _ e)         = concatMap grapDep  e
        dep (CoreUnfolding {uf_tmpl = e}) = grapDep  e
        dep _                             = []

        grapDep :: CoreExpr -> [Id]
        grapDep e           = freeVars S.empty e

updateDynFlags cfg
  = do df <- getSessionDynFlags
       let df' = df { importPaths  = idirs cfg ++ importPaths df
                    , libraryPaths = idirs cfg ++ libraryPaths df
                    , includePaths = idirs cfg ++ includePaths df
                    , profAuto     = ProfAutoCalls
                    , ghcLink      = LinkInMemory
                    --FIXME: this *should* be HscNothing, but that prevents us from
                    -- looking up *unexported* names in another source module..
                    , hscTarget    = HscInterpreted -- HscNothing
                    , ghcMode      = CompManager
                    -- prevent GHC from printing anything
                    , log_action   = \_ _ _ _ _ -> return ()
                    -- , verbosity = 3
                    } `xopt_set` Opt_MagicHash
                  --     `gopt_set` Opt_Hpc
                      `gopt_set` Opt_ImplicitImportQualified
                      `gopt_set` Opt_PIC
#if __GLASGOW_HASKELL__ >= 710
                      `gopt_set` Opt_Debug
#endif
       (df'',_,_) <- parseDynamicFlags df' (map noLoc $ ghcOptions cfg)
       setSessionDynFlags $ df'' -- {profAuto = ProfAutoAll}

compileCFiles cfg
  = do df  <- getSessionDynFlags
       setSessionDynFlags $ df { includePaths = nub $ idirs cfg ++ includePaths df
                               , importPaths  = nub $ idirs cfg ++ importPaths df
                               , libraryPaths = nub $ idirs cfg ++ libraryPaths df }
       hsc <- getSession
       os  <- mapM (\x -> liftIO $ compileFile hsc StopLn (x,Nothing)) (nub $ cFiles cfg)
       df  <- getSessionDynFlags
       setSessionDynFlags $ df { ldInputs = map (FileOption "") os ++ ldInputs df }


mgi_namestring = moduleNameString . moduleName . mgi_module

importVars            = freeVars S.empty

definedVars           = concatMap defs
  where
    defs (NonRec x _) = [x]
    defs (Rec xes)    = map fst xes


------------------------------------------------------------------
-- | Extracting CoreBindings From File ---------------------------
------------------------------------------------------------------
getGhcModGuts1 :: FilePath -> Ghc MGIModGuts
getGhcModGuts1 fn = do
   modGraph <- getModuleGraph
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       -- mod_guts <- modSummaryModGuts modSummary
       mod_p    <- parseModule modSummary
       mod_guts <- coreModule <$> (desugarModule =<< typecheckModule (ignoreInline mod_p))
       let deriv = getDerivedDictionaries mod_guts 
       return   $! (miModGuts (Just deriv) mod_guts)
     Nothing     -> exitWithPanic "Ghc Interface: Unable to get GhcModGuts"

getDerivedDictionaries cm = instEnvElts $ mg_inst_env cm

cleanFiles :: FilePath -> IO ()
cleanFiles fn
  = do forM_ bins (tryIgnore "delete binaries" . removeFileIfExists)
       tryIgnore "create temp directory" $ createDirectory dir
    where
       bins = replaceExtension fn <$> ["hi", "o"]
       dir  = tempDirectory fn


removeFileIfExists f = doesFileExist f >>= (`when` removeFile f)

--------------------------------------------------------------------------------
-- | Desugaring (Taken from GHC, modified to hold onto Loc in Ticks) -----------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- | Extracting Qualifiers -----------------------------------------------------
--------------------------------------------------------------------------------

moduleHquals mg paths target imps incs
  = do hqs   <- specIncludes Hquals paths incs
       hqs'  <- moduleImports [Hquals] paths (mgi_namestring mg : imps)
       hqs'' <- liftIO   $ filterM doesFileExist [extFileName Hquals target]
       let rv = sortNub  $ hqs'' ++ hqs ++ (snd <$> hqs')
       liftIO $ whenLoud $ putStrLn $ "Reading Qualifiers From: " ++ show rv
       return rv

--------------------------------------------------------------------------------
-- | Extracting Specifications (Measures + Assumptions) ------------------------
--------------------------------------------------------------------------------

moduleSpec cfg cbs vars defVars target mg tgtSpec logicmap impSpecs
  = do addImports  impSpecs
       addContext  $ IIModule $ moduleName $ mgi_module mg
       env        <- getSession
       let specs   = (target,tgtSpec):impSpecs
       let imps    = sortNub $ impNames ++ [ symbolString x
                                           | (_,spec) <- specs
                                           , x <- Ms.imports spec
                                           ]
       ghcSpec    <- liftIO $ makeGhcSpec cfg target cbs vars defVars exports env logicmap specs
       return      (ghcSpec, imps, Ms.includes tgtSpec)
    where
      exports    = mgi_exports mg
      impNames   = map (getModString.fst) impSpecs
      addImports = mapM (addContext . IIDecl . qualImportDecl . getModName . fst)

allDepNames = concatMap (map declNameString . ms_textual_imps)

declNameString = moduleNameString . unLoc . ideclName . unLoc

patErrorName    = "PatErr"
realSpecName    = "Real"
notRealSpecName = "NotReal"

getSpecs rflag tflag target paths names exts
  = do fs'     <- sortNub <$> moduleImports exts paths names
       patSpec <- getPatSpec paths tflag
       rlSpec  <- getRealSpec paths rflag
       let fs  = patSpec ++ rlSpec ++ fs'
       liftIO  $ whenLoud $ putStrLn ("getSpecs: " ++ show fs)
       transParseSpecs exts paths (S.singleton target) mempty (map snd fs)

getPatSpec paths totalitycheck
  | totalitycheck
  = (map (patErrorName, )) . maybeToList <$> moduleFile paths patErrorName Spec
  | otherwise
  = return []

getRealSpec paths freal
  | freal
  = (map (realSpecName, )) . maybeToList <$> moduleFile paths realSpecName Spec
  | otherwise
  = (map (notRealSpecName, )) . maybeToList <$> moduleFile paths notRealSpecName Spec

transParseSpecs _ _ _ specs []
  = return specs
transParseSpecs exts paths seenFiles specs newFiles
  = do newSpecs  <- liftIO $ mapM (\f -> addFst3 f <$> parseSpec f) newFiles
       impFiles  <- moduleImports exts paths $ specsImports newSpecs
       let seenFiles' = seenFiles  `S.union` (S.fromList newFiles)
       let specs'     = specs ++ map (third noTerm) newSpecs
       let newFiles'  = [f | (_,f) <- impFiles, not (f `S.member` seenFiles')]
       transParseSpecs exts paths seenFiles' specs' newFiles'
  where
    specsImports ss = nub $ concatMap (map symbolString . Ms.imports . thd3) ss
    noTerm spec = spec { Ms.decr=mempty, Ms.lazy=mempty, Ms.termexprs=mempty }
    third f (a,b,c) = (a,b,f c)

parseSpec :: FilePath -> IO (ModName, Ms.BareSpec)
parseSpec file
  = do whenLoud $ putStrLn $ "parseSpec: " ++ file
       either Ex.throw return . specParser file =<< readFile file

specParser file str
  | isExtFile Spec file  = specSpecificationP file str
  | isExtFile Hs file    = hsSpecificationP   file str
  | isExtFile LHs file   = lhsSpecificationP  file str
  | otherwise            = exitWithPanic $ "SpecParser: Cannot Parse File " ++ file

moduleImports :: GhcMonad m => [Ext] -> [FilePath] -> [String] -> m [(String, FilePath)]
moduleImports exts paths names
  = liftM concat $ forM names $ \name -> do
      map (name,) . catMaybes <$> mapM (moduleFile paths name) exts

moduleFile :: GhcMonad m => [FilePath] -> String -> Ext -> m (Maybe FilePath)
moduleFile paths name ext
  | ext `elem` [Hs, LHs]
  = do mg <- getModuleGraph
       case find ((==name) . moduleNameString . ms_mod_name) mg of
         Nothing -> liftIO $ getFileInDirs (extModuleName name ext) paths
         Just ms -> return $ normalise <$> ml_hs_file (ms_location ms)
  | otherwise
  = liftIO $ getFileInDirs (extModuleName name ext) paths

specIncludes :: GhcMonad m => Ext -> [FilePath] -> [FilePath] -> m [FilePath]
specIncludes ext paths reqs
  = do let libFile  = extFileNameR ext $ symbolString preludeName
       let incFiles = catMaybes $ reqFile ext <$> reqs
       liftIO $ forM (libFile : incFiles) $ \f -> do
         mfile <- getFileInDirs f paths
         case mfile of
           Just file -> return file
           Nothing -> errorstar $ "cannot find " ++ f ++ " in " ++ show paths

reqFile ext s
  | isExtFile ext s
  = Just s
  | otherwise
  = Nothing





instance PPrint GhcSpec where
  pprint spec =  (text "******* Target Variables ********************")
              $$ (pprint $ tgtVars spec)
              $$ (text "******* Type Signatures *********************")
              $$ (pprintLongList $ tySigs spec)
              $$ (text "******* Assumed Type Signatures *************")
              $$ (pprintLongList $ asmSigs spec)
              $$ (text "******* DataCon Specifications (Measure) ****")
              $$ (pprintLongList $ ctors spec)
              $$ (text "******* Measure Specifications **************")
              $$ (pprintLongList $ meas spec)

instance PPrint GhcInfo where
  pprint info =   (text "*************** Imports *********************")
              $+$ (intersperse comma $ text <$> imports info)
              $+$ (text "*************** Includes ********************")
              $+$ (intersperse comma $ text <$> includes info)
              $+$ (text "*************** Imported Variables **********")
              $+$ (pprDoc $ impVars info)
              $+$ (text "*************** Defined Variables ***********")
              $+$ (pprDoc $ defVars info)
              $+$ (text "*************** Specification ***************")
              $+$ (pprint $ spec info)
              $+$ (text "*************** Core Bindings ***************")
              $+$ (pprint $ cbs info)

instance Show GhcInfo where
  show = showpp

instance PPrint [CoreBind] where
  pprint = pprDoc . tidyCBs

instance PPrint TargetVars where
  pprint AllVars   = text "All Variables"
  pprint (Only vs) = text "Only Variables: " <+> pprint vs

------------------------------------------------------------------------
-- Dealing With Errors -------------------------------------------------
------------------------------------------------------------------------

-- | Throw a panic exception
exitWithPanic  :: String -> a
exitWithPanic  = Ex.throw . errOther . text

-- | Convert a GHC error into one of ours
instance Result SourceError where
  result = (`Crash` "Invalid Source")
         . concatMap errMsgErrors
         . bagToList
         . srcErrorMessages

errMsgErrors e = [ ErrGhc (errMsgSpan e) (pprint e)]
