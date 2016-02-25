{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Haskell.Liquid.GHC.Interface (

  -- * extract all information needed for verification
    getGhcInfo

  -- * printer
  , pprintCBs
  ) where

import Prelude hiding (error)
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
import Control.Monad (unless, filterM, foldM, when, forM, forM_, liftM)
import Data.List (find, nub, (\\))
import Data.Maybe (catMaybes, maybeToList)
import qualified Data.HashSet        as S

import System.Console.CmdArgs.Verbosity (whenLoud, whenNormal)
import System.Directory (removeFile, createDirectoryIfMissing, doesFileExist)
import Language.Fixpoint.Types hiding (Error, Result, Expr)
import Language.Fixpoint.Misc

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.UX.Errors
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types.PrettyPrint
import Language.Haskell.Liquid.Types.Visitors
import Language.Haskell.Liquid.UX.CmdLine (withPragmas)
import Language.Haskell.Liquid.UX.Cabal   (withCabal)
import Language.Haskell.Liquid.UX.Tidy
import Language.Haskell.Liquid.Parse
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Fixpoint.Utils.Files
import Language.Haskell.Liquid.Types.Errors


--------------------------------------------------------------------------------
getGhcInfo :: Maybe HscEnv -> Config -> FilePath -> IO (GhcInfo, HscEnv)
--------------------------------------------------------------------------------
getGhcInfo = getGhcInfo'

addRootTarget x = setTargets [x]


getGhcInfo' :: Maybe HscEnv -> Config -> FilePath -> IO (GhcInfo, HscEnv)
getGhcInfo' hEnv cfg f
  = runGhc (Just libdir) $ {- repM 3 -} do
      _     <- setSessionMb hEnv
      df    <- getDynFlags
      info  <- defaultCleanupHandler df $ getGhcInfo'' cfg f
      hEnv' <- getSession
      return (info, hEnv')

setSessionMb :: Maybe HscEnv -> Ghc ()
setSessionMb Nothing  = return ()
setSessionMb (Just e) = setSession e


getGhcInfo'' :: Config -> FilePath -> Ghc GhcInfo
getGhcInfo'' cfg0 target
  = {- runGhc (Just libdir) $ -} do
      liftIO              $ cleanFiles target
      liftIO $ whenNormal $ donePhase Loud "Cleaned Files"
      addRootTarget     =<< guessTarget target Nothing
      (name, tgtSpec)    <- liftIO $ parseSpec target
      cfg                <- liftIO $ withPragmas cfg0 target $ Ms.pragmas tgtSpec
      cfg                <- liftIO $ withCabal cfg
      let paths           = idirs cfg
      _                  <- updateDynFlags cfg
      liftIO              $ whenLoud $ putStrLn ("paths = " ++ show paths)
      let name'           = ModName Target (getModName name)
      impNames           <- allDepNames <$> depanal [] False
      impSpecs           <- getSpecs (not $ linear cfg) (totality cfg) target paths impNames [Spec, Hs, LHs]
      liftIO $ whenNormal $ donePhase Loud "Parsed All Specifications"
      compileCFiles      =<< liftIO (foldM (\c (f,_,s) -> withPragmas c f (Ms.pragmas s)) cfg impSpecs)
      impSpecs'          <- forM impSpecs $ \(f, n, s) -> do
                              unless (isSpecImport n) $
                                addTarget =<< guessTarget f Nothing
                              return (n,s)
      load LoadAllTargets
      liftIO $ whenNormal $ donePhase Loud "Loaded Targets"
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
      let derVs           = derivedVars coreBinds $ ((is_dfun <$>) <$>) $ mgi_cls_inst modguts
      logicmap           <- liftIO makeLogicMap
      (spc, imps, incs)  <- moduleSpec cfg coreBinds (impVs ++ defVs) letVs name' modguts tgtSpec logicmap impSpecs'
      liftIO              $ whenLoud $ putStrLn $ "Module Imports: " ++ show imps
      hqualFiles         <- moduleHquals modguts paths target imps incs
      return              $ GI target hscEnv coreBinds derVs impVs (letVs ++ datacons) useVs hqualFiles imps incs spc

makeLogicMap = do
  lg    <- getCoreToLogicPath
  lspec <- readFile lg
  return $ parseSymbolToLogic lg lspec

classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: CoreProgram -> Maybe [DFunId] -> [Id]
derivedVars cBinds (Just fds) = concatMap (derivedVs cBinds) fds
derivedVars _      Nothing    = []

derivedVs :: CoreProgram -> DFunId -> [Id]
derivedVs cBinds fd = concatMap bindersOf cBinds' ++ deps
  where
    cBinds'         = filter f cBinds
    f (NonRec x _)  = eqFd x
    f (Rec xes   )  = any eqFd (fst <$> xes)
    eqFd x          = varName x == varName fd
    deps            = concatMap unfoldDep unfolds
    unfolds         = unfoldingInfo . idInfo <$> concatMap bindersOf cBinds'

unfoldDep :: Unfolding -> [Id]
unfoldDep (DFunUnfolding _ _ e)         = concatMap exprDep  e
unfoldDep (CoreUnfolding {uf_tmpl = e}) = exprDep  e
unfoldDep _                             = []

exprDep :: CoreExpr -> [Id]
exprDep = freeVars S.empty

{- ORIG -}
updateDynFlags cfg
  = do df <- getSessionDynFlags
       let df' = df { importPaths  = idirs cfg ++ importPaths df
                    , libraryPaths = idirs cfg ++ libraryPaths df
                    , includePaths = idirs cfg ++ includePaths df
                    -- , profAuto     = ProfAutoCalls
                    , ghcLink      = LinkInMemory
                    --FIXME: this *should* be HscNothing, but that prevents us from
                    -- looking up *unexported* names in another source module..
                    , hscTarget    = HscInterpreted -- HscNothing
                    , ghcMode      = CompManager
                    -- prevent GHC from printing anything
                    , log_action   = \_ _ _ _ _ -> return ()
                    -- , verbosity = 2
                    } `xopt_set` Opt_MagicHash
                  --     `gopt_set` Opt_Hpc
                      `gopt_set` Opt_ImplicitImportQualified
                      `gopt_set` Opt_PIC
                      -- `gopt_set` Opt_Debug
       (df'',_,_) <- parseDynamicFlags df' (map noLoc $ ghcOptions cfg)
       setSessionDynFlags df''


{- hdevtools
updateDynFlags cfg = do
  initialDynFlags <- GHC.getSessionDynFlags
  let updatedDynFlags = initialDynFlags
                        { GHC.ghcLink       = GHC.NoLink
                        -- , GHC.log_action    = \ _ _ _ _ _ -> return () -- logAction state clientSend
                        , GHC.hscTarget     = GHC.HscInterpreted
                        }
  (finalDynFlags, _, _) <- GHC.parseDynamicFlags updatedDynFlags (map GHC.noLoc hackOptions{- $ ghcOptions cfg -})
  -- HEREHERE
  -- liftIO $ writeFile "/Users/rjhala/tmp/hdevtools.log" (show ghcOpts)
  _ <- GHC.setSessionDynFlags finalDynFlags
  return ()
-}

{- TODO: unused
hackOptions :: [String]
hackOptions =
  [ "-w"
  , "-v0"
  , "-fbuilding-cabal-package"
  , "-O"
  , "-outputdir"
  , ".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  , "-odir"
  , ".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  , "-hidir"
  , ".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  , "-stubdir"
  , ".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  , "-i"
  , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/src"
  , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/include"
  -- , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/."
  , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  -- , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/tests"
  , "-i/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen"
  , "-I.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen"
  , "-I.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
  , "-optP-include"
  , "-optP.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen/cabal_macros.h"
  , "-hide-all-packages"
  , "-no-user-package-db"
  , "-package-db"
  , "/Applications/ghc-7.10.2.app/Contents/lib/ghc-7.10.2/package.conf.d"
  , "-package-db"
  , "/Users/rjhala/.stack/snapshots/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb"
  , "-package-db"
  , "/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/install/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb"
  , "-package-id"
  , "Cabal-1.22.4.0-43515548ac8e8e693b550dcfa1b04e2b"
  , "-package-id"
  , "Diff-0.3.2-d60e738085e24bd2ba085853867b84a6"
  , "-package-id"
  , "aeson-0.9.0.1-ea82995047cb231c94231aee293436ee"
  , "-package-id"
  , "array-0.5.1.0-d4206b835b96b5079d918fa1eab1a9a8"
  , "-package-id"
  , "bifunctors-5-9497b78c1808987b8601618de2742b5c"
  , "-package-id"
  , "cpphs-1.19.3-21d69634848f44bbddd2385456c13030"
  , "-package-id"
  , "fingertree-0.1.1.0-e8cb817ba02a5ed615b3a46f18f3fd8f"
  , "-package-id"
  , "ghc-paths-0.1.0.9-b18f6718b3226041485a4e0a0842c180"
  , "-package-id"
  , "hashable-1.2.3.3-09c4177c49dd46a63f7036317bb17114"
  , "-package-id"
  , "hpc-0.6.0.2-49bce407db3f37807645ac03c42b8ff3"
  , "-package-id"
  , "hscolour-1.23-77c6937e0747fc7892d42aa452545b51"
  , "-package-id"
  , "parsec-3.1.9-bddea73c8bf2d5ff1335dae2cc92e789"
  , "-package-id"
  , "syb-0.5.1-09089498a055bd723b4a95c1351d3c8a"
  , "-package-id"
  , "template-haskell-2.10.0.0-161ca39a5ae657ff216d049e722e60ea"
  , "-package-id"
  , "text-1.2.1.3-2395ef415c1b20175aae83b50060e389"
  , "-package-id"
  , "time-1.5.0.1-710377a9566ae0edafdde8dc74a184c3"
  , "-package-id"
  , "vector-0.10.12.3-67219b7cb09d19688dca52e92595a7d6"
  , "-package-id"
  , "bytestring-0.10.6.0-6e8453cb70b477776f26900f41a5e17a"
  , "-package-id"
  , "cereal-0.4.1.1-e7af0306d1317407815a09e40431fc3f"
  , "-package-id"
  , "cmdargs-0.10.13-a8aec3840014c1a2b642b8ee0671d451"
  , "-package-id"
  , "daemons-0.2.1-0b0661a02074f525101355cceebca33b"
  , "-package-id"
  , "data-default-0.5.3-a2ece8050e447d921b001e26e14476f2"
  , "-package-id"
  , "deepseq-1.4.1.1-5de90d6c626db2476788444fb08c1eb3"
  , "-package-id"
  , "ghc-7.10.2-5c2381785a7b22838c6eda985bc898cf"
  , "-package-id"
  , "ghc-options-0.2.0.1-58eda4323c55c86764b7c99a83ab50a1"
  , "-package-id"
  , "liquid-fixpoint-0.6-c5ff693cb49202144ed67af52435a9b7"
  , "-package-id"
  , "network-2.6.2.1-54f9bbbc4dc78b945fb82127414a5b82"
  , "-package-id"
  , "pretty-1.1.2.0-1d31b75e6aa28069010db3db8ab24535"
  , "-package-id"
  , "prover-0.1.0.0-af42484d037d94d0e2b5c21591019282"
  , "-package-id"
  , "unix-2.7.1.0-75051e1ddce506fe76a9ea932b926357"
  , "-package-id"
  , "unordered-containers-0.2.5.1-09ed02f61ed89449c8cd4b51d7f295c2"
  , "-package-id"
  , "base-4.8.1.0-075aa0db10075facc5aaa59a7991ca2f"
  , "-package-id"
  , "containers-0.5.6.2-2b49cce16f8a2908df8454387e550b93"
  , "-package-id"
  , "directory-1.2.2.0-16f6a661d4e92cd8da4d681a1d197064"
  , "-package-id"
  , "filepath-1.4.0.0-8fee9c13b5e42926cc01f6aa7c403c4b"
  , "-package-id"
  , "mtl-2.2.1-5cf332b11edb88a6040af20fd6a58acb"
  , "-package-id"
  , "optparse-applicative-0.11.0.2-64c4a013db45b66a7b578a0a518d7f3d"
  , "-package-id"
  , "process-1.2.3.0-36e5501145ab363f58c5e5a7079e9636"
  , "-package-id"
  , "stm-2.4.4-2526ff89874f899372b2e4f544bb03cd"
  , "-package-id"
  , "tagged-0.8.1-8fb7724b78ef88e44ca8950c77a173f6"
  , "-package-id"
  , "tasty-0.10.1.2-3edf1ce479f2dc1472803ce20060e1e3"
  , "-package-id"
  , "tasty-hunit-0.9.2-dc3e487b6addcc5acb2e3cf6fcd6ae50"
  , "-package-id"
  , "tasty-rerun-1.1.5-69a2e8be39919b24c991bdcc6778a213"
  , "-package-id"
  , "transformers-0.4.2.0-21dcbf13c43f5d8cf6a1f54dee6c5bff"
  , "-XHaskell98"
  , "-XPatternGuards"
  , "-W"
  , "-fno-warn-unused-imports"
  , "-fno-warn-dodgy-imports"
  , "-fno-warn-deprecated-flags"
  , "-fno-warn-deprecations"
  , "-fno-warn-missing-methods"
  , "-O2"
  , "-threaded"
  , "-O0"
  , "-Wall"]
-}



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
   case find (\m -> not (isBootSummary m) && fn == msHsFilePath m) modGraph of
     Just modSummary -> do
       mod_p    <- parseModule modSummary
       mod_guts <- coreModule <$> (desugarModule =<< typecheckModule (ignoreInline mod_p))
       let deriv = getDerivedDictionaries mod_guts
       return   $! miModGuts (Just deriv) mod_guts
     Nothing ->
       panic Nothing $ "Ghc Interface: Unable to get GhcModGuts"

getDerivedDictionaries cm = instEnvElts $ mg_inst_env cm

cleanFiles :: FilePath -> IO ()
cleanFiles fn
  = do forM_ bins (tryIgnore "delete binaries" . removeFileIfExists)
       tryIgnore "create temp directory" $ createDirectoryIfMissing False dir
    where
       bins = replaceExtension fn <$> ["hi", "o"]
       dir  = tempDirectory fn

removeFileIfExists f = doesFileExist f >>= (`when` removeFile f)

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

moduleSpec cfg cBinds vars dVars tgtMod mg tgtSpec logicmap impSpecs
  = do _          <- addImports  impSpecs
       addContext  $ IIModule $ moduleName $ mgi_module mg
       gEnv        <- getSession
       let specs   = (tgtMod, tgtSpec):impSpecs
       let imps    = sortNub $ impNames ++ [ symbolString x
                                           | (_, sp) <- specs
                                           , x <- Ms.imports sp
                                           ]
       ghcSpec    <- liftIO $ makeGhcSpec cfg tgtMod cBinds vars dVars exports gEnv logicmap specs
       return      (ghcSpec, imps, Ms.includes tgtSpec)
    where
      exports    = mgi_exports mg
      impNames   = map (getModString.fst) impSpecs
      addImports = mapM_ (addContext . IIDecl . qualImportDecl . getModName . fst)

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
       transParseSpecs exts paths (S.singleton target) mempty
                       -- NOTE: remove target from the initial list of specs
                       -- in case of cyclic dependencies with hs-boot files
                       (map snd fs \\ [target])

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

specParser f str
  | isExtFile Spec   f = specSpecificationP f str
  | isExtFile Hs     f = hsSpecificationP   f str
  | isExtFile HsBoot f = hsSpecificationP   f str
  | isExtFile LHs    f = lhsSpecificationP  f str
  | otherwise          = panic Nothing $ "SpecParser: Cannot Parse File " ++ f


moduleImports :: GhcMonad m => [Ext] -> [FilePath] -> [String] -> m [(String, FilePath)]
moduleImports exts paths names
  = liftM concat $ forM names $ \name -> do
      map (name,) . catMaybes <$> mapM (moduleFile paths name) exts

moduleFile :: GhcMonad m => [FilePath] -> String -> Ext -> m (Maybe FilePath)
moduleFile paths name ext
  | ext `elem` [Hs, LHs]
  = do mg <- getModuleGraph
       case find (\m -> not (isBootSummary m) &&
                        name == moduleNameString (ms_mod_name m)) mg of
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
           Nothing -> panic Nothing $ "cannot find " ++ f ++ " in " ++ show paths

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
              $+$ (pprintCBs $ cbs info)

pprintCBs :: [CoreBind] -> Doc
pprintCBs = pprDoc . tidyCBs

instance Show GhcInfo where
  show = showpp

instance PPrint TargetVars where
  pprint AllVars   = text "All Variables"
  pprint (Only vs) = text "Only Variables: " <+> pprint vs

------------------------------------------------------------------------
-- | Dealing With Errors -------------------------------------------------
------------------------------------------------------------------------
-- | Convert a GHC error into one of ours
instance Result SourceError where
  result = (`Crash` "Invalid Source")
         . concatMap errMsgErrors
         . bagToList
         . srcErrorMessages

errMsgErrors e = [ ErrGhc (errMsgSpan e) (pprint e)]
