
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables #-}

module Language.Haskell.Liquid.GhcInterface (
  
  -- * extract all information needed for verification
    getGhcInfo

  -- * visitors 
  , CBVisitable (..) 
  ) where

import GHC 
import Text.PrettyPrint.HughesPJ
import HscTypes
import TidyPgm      (tidyProgram)
import Literal
import CoreSyn

import Var
import Name         (getSrcSpan)
import CoreMonad    (liftIO)
import DataCon
import qualified TyCon as TC
import HscMain
import Module
import Language.Haskell.Liquid.Desugar.HscMain (hscDesugarWithLoc) 
import qualified Control.Exception as Ex

import GHC.Paths (libdir)
import System.FilePath (dropExtension, takeFileName, splitFileName, combine,
                        dropFileName, normalise)

import DynFlags
import Control.Arrow (second)
import Control.Monad (filterM, zipWithM, when, forM, liftM)
import Control.DeepSeq
import Control.Applicative  hiding (empty)
import Data.Monoid hiding ((<>))
import Data.List (intercalate, foldl', find, (\\), nub)
import Data.Maybe (catMaybes)
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import System.Directory (doesFileExist)
import Language.Fixpoint.Types hiding (Expr) 
import Language.Fixpoint.Misc

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.ANFTransform
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Resolution (resolveSpec, qualImportDecl, addContext)

import Language.Haskell.Liquid.Parse 
import Language.Fixpoint.Parse          hiding (brackets, comma)
import Language.Fixpoint.Names
import Language.Fixpoint.Files

import qualified Language.Haskell.Liquid.Measure as Ms


------------------------------------------------------------------
getGhcInfo :: Config -> FilePath -> IO GhcInfo
------------------------------------------------------------------

getGhcInfo cfg target 
  = runGhc (Just libdir)  $ do
      liftIO $ deleteBinFiles target
      df                 <- getSessionDynFlags
      setSessionDynFlags  $ updateDynFlags df (idirs cfg) 
      addTarget =<< guessTarget target Nothing
      (_,name,tgtSpec)   <- liftIO $ parseSpec target
      impNames           <- allDepNames <$> depanal [] False
      impSpecs           <- getSpecs paths impNames [Spec, Hs, LHs]
      forM impSpecs $ \(f,n,_) -> when (not $ isExtFile Spec f) $ do
          addTarget =<< guessTarget f Nothing
      load LoadAllTargets
      modguts            <- getGhcModGuts1 target
      hscEnv             <- getSession
      coreBinds          <- liftIO $ anormalize hscEnv modguts
      let impVs           = importVars  coreBinds 
      let defVs           = definedVars coreBinds 
      let useVs           = readVars    coreBinds
      let letVs           = letVars     coreBinds
      liftIO              $ putStrLn ("paths = " ++ show paths)
      (spec, imps, incs) <- moduleSpec cfg (impVs ++ defVs) letVs target modguts tgtSpec impSpecs
      liftIO              $ putStrLn $ "Module Imports: " ++ show imps 
      hqualFiles         <- moduleHquals modguts (idirs cfg) target imps incs 
      return              $ GI hscEnv coreBinds impVs defVs useVs hqualFiles imps incs spec 
  where
    paths = idirs cfg
    trace = liftIO . putStrLn . showpp


updateDynFlags df ps 
  = df { importPaths  = ps ++ importPaths df  } 
       { libraryPaths = ps ++ libraryPaths df }
       { profAuto     = ProfAutoCalls         }
       { ghcLink      = NoLink                }
       { hscTarget    = HscNothing            }
       `xopt_set` Opt_MagicHash

printVars s vs 
  = do putStrLn s 
       putStrLn $ showPpr [(v, getSrcSpan v) | v <- vs]

mgi_namestring = moduleNameString . moduleName . mgi_module

importVars            = freeVars S.empty 

definedVars           = concatMap defs 
  where 
    defs (NonRec x _) = [x]
    defs (Rec xes)    = map fst xes


------------------------------------------------------------------
-- | Extracting CoreBindings From File ---------------------------
------------------------------------------------------------------

getGhcModGuts1 fn = do
   modGraph <- getModuleGraph -- depanal [] True
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       mod_guts <- coreModule `fmap` (desugarModuleWithLoc =<< typecheckModule =<< parseModule modSummary)
       return   $! (miModGuts mod_guts)
     Nothing         -> error "GhcInterface : getGhcModGuts1"

-- Generates Simplified ModGuts (INLINED, etc.) but without SrcSpan
getGhcModGutsSimpl1 fn = do
   modGraph <- getModuleGraph -- depanal [] True
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       mod_guts   <- coreModule `fmap` (desugarModule =<< typecheckModule =<< parseModule modSummary)
       hsc_env    <- getSession
       simpl_guts <- liftIO $ hscSimplify hsc_env mod_guts
       (cg,_)     <- liftIO $ tidyProgram hsc_env simpl_guts
       liftIO $ putStrLn "************************* CoreGuts ****************************************"
       liftIO $ putStrLn (showPpr $ cg_binds cg)
       return $! (miModGuts mod_guts) { mgi_binds = cg_binds cg } 
     Nothing         -> error "GhcInterface : getGhcModGutsSimpl1"

peepGHCSimple fn 
  = do z <- compileToCoreSimplified fn
       liftIO $ putStrLn "************************* peepGHCSimple Core Module ************************"
       liftIO $ putStrLn $ showPpr z
       liftIO $ putStrLn "************************* peepGHCSimple Bindings ***************************"
       liftIO $ putStrLn $ showPpr (cm_binds z)
       errorstar "Done peepGHCSimple"

--------------------------------------------------------------------------------
-- | Desugaring (Taken from GHC, modified to hold onto Loc in Ticks) -----------
--------------------------------------------------------------------------------

desugarModuleWithLoc tcm = do
  let ms = pm_mod_summary $ tm_parsed_module tcm 
  -- let ms = modSummary tcm
  let (tcg, _) = tm_internals_ tcm
  hsc_env <- getSession
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  guts <- liftIO $ hscDesugarWithLoc hsc_env_tmp ms tcg
  return $ DesugaredModule { dm_typechecked_module = tcm, dm_core_module = guts }

--------------------------------------------------------------------------------
-- | Extracting Qualifiers -----------------------------------------------------
--------------------------------------------------------------------------------

moduleHquals mg paths target imps incs 
  = do hqs   <- specIncludes Hquals paths incs 
       hqs'  <- moduleImports [Hquals] paths (mgi_namestring mg : imps)
       hqs'' <- liftIO   $ filterM doesFileExist [extFileName Hquals target]
       let rv = sortNub  $ hqs'' ++ hqs ++ (snd <$> hqs')
       liftIO $ putStrLn $ "Reading Qualifiers From: " ++ show rv 
       return rv

--------------------------------------------------------------------------------
-- | Extracting Specifications (Measures + Assumptions) ------------------------
--------------------------------------------------------------------------------
 
moduleSpec cfg vars defVars target mg tgtSpec impSpecs
  = do addImports impSpecs
       addContext $ IIModule $ moduleName $ mgi_module mg
       env <- getSession
       let specs   = (target,name,tgtSpec):impSpecs
       let rtenv   = Ms.makeRTEnv (concatMap (Ms.aliases  . thd3) specs)
                                  (concatMap (Ms.paliases . thd3) specs)
       let specs' = [ (n', Ms.expandRTAliases rtenv s)
                    | (f,n,s) <- specs
                    , let n' = if isExtFile Spec f then "" else n
                    ]
       let imps    = sortNub $ impNames ++ [ symbolString x
                                           | (_,spec) <- specs'
                                           , x <- Ms.imports spec
                                           ]
       getContext >>= liftIO . putStrLn . showPpr
       ghcSpec <- liftIO $ makeGhcSpec cfg name vars defVars env specs'
       return      (ghcSpec, imps, Ms.includes tgtSpec)
    where
      trace = liftIO . putStrLn . showpp
      name     = mgi_namestring mg
      impNames = map snd3 impSpecs
      addImports is
        = mapM (addContext . IIDecl . qualImportDecl . mkModuleName) (map snd3 is)



allDepNames = concatMap (map declNameString . ms_textual_imps)

declNameString = moduleNameString . unLoc . ideclName . unLoc

depNames       = map fst        . dep_mods      . mgi_deps
dirImportNames = map moduleName . moduleEnvKeys . mgi_dir_imps  
targetName     = dropExtension  . takeFileName 
-- starName fn    = combine dir ('*':f) where (dir, f) = splitFileName fn
starName       = ("*" ++)


getSpecs paths names exts
  = do fs    <- sortNub <$> moduleImports exts paths names 
       liftIO $ putStrLn ("getSpecs: " ++ show fs)
       transParseSpecs exts paths S.empty mempty (map snd fs)

transParseSpecs _ _ _ specs []
  = return specs
transParseSpecs exts paths seenFiles specs newFiles
  = do newSpecs  <- liftIO $ mapM parseSpec newFiles
       impFiles  <- moduleImports exts paths $ specsImports newSpecs
       let seenFiles' = seenFiles  `S.union` (S.fromList newFiles)
       let specs'     = specs ++ map (third noTerm) newSpecs
       let newFiles'  = [f | (_,f) <- impFiles, not (f `S.member` seenFiles')]
       transParseSpecs exts paths seenFiles' specs' newFiles'
  where
    specsImports ss = nub $ concatMap (map symbolString . Ms.imports . thd3) ss
    noTerm spec = spec { Ms.decr=mempty, Ms.lazy=mempty }
    third f (a,b,c) = (a,b,f c)

parseSpec file
  = Ex.catch (parseSpec' file) $ \(e :: Ex.IOException) ->
         ioError $ userError $ "Hit exception: " ++ (show e)
                            ++ " while parsing Spec file: " ++ file

parseSpec' file
  = do str            <- readFile file
       let (name,spec) = specParser file str
       putStrLn $ "parseSpec: " ++ file ++ " for module " ++ name
       return $ (file,name,spec)

specParser file str
  | isExtFile Spec file  = rr' file str
  | isExtFile Hs file    = hsSpecificationP file str
  | isExtFile LHs file   = hsSpecificationP file str
  | otherwise            = errorstar $ "specParser: Cannot Parse File " ++ file

--specParser Spec _  = rr'
--specParser Hs name = hsSpecificationP name

--moduleImports ext paths  = liftIO . liftM catMaybes . mapM (mnamePath paths ext) 
--mnamePath paths ext name = fmap (name,) <$> getFileInDirs file paths
--                           where file = name `extModuleName` ext

moduleImports :: GhcMonad m => [Ext] -> [FilePath] -> [String] -> m [(String, FilePath)]
moduleImports exts paths names
  = do modGraph <- getModuleGraph
       liftM concat $ forM names $ \name -> do
         map (name,) . catMaybes <$> mapM (moduleFile paths name) exts

moduleFile :: GhcMonad m => [FilePath] -> String -> Ext -> m (Maybe FilePath)
moduleFile paths name ext
  | ext `elem` [Hs, LHs]
  = do mg <- getModuleGraph
       case find ((==name) . moduleNameString . ms_mod_name) mg of
         Nothing -> liftIO $ getFileInDirs (extModuleName name ext) paths
         Just ms -> return $ normalise <$> ml_hs_file (ms_location ms)
  | otherwise
  = do liftIO $ getFileInDirs (extModuleName name ext) paths

isJust Nothing = False
isJust (Just a) = True

--moduleImports ext paths names 
--  = liftIO $ liftM catMaybes $ forM extNames (namePath paths)
--    where extNames = (`extModuleName` ext) <$> names 
-- namePath paths fileName = getFileInDirs fileName paths

--namePath_debug paths name 
--  = do res <- getFileInDirs name paths
--       case res of
--         Just p  -> putStrLn $ "namePath: name = " ++ name ++ " expanded to: " ++ (show p) 
--         Nothing -> putStrLn $ "namePath: name = " ++ name ++ " not found in: " ++ (show paths)
--       return res

specIncludes :: GhcMonad m => Ext -> [FilePath] -> [FilePath] -> m [FilePath]
specIncludes ext paths reqs 
  = do let libFile  = extFileName ext preludeName
       let incFiles = catMaybes $ reqFile ext <$> reqs 
       liftIO $ forM (libFile : incFiles) (`findFileInDirs` paths)

reqFile ext s 
  | isExtFile ext s 
  = Just s 
  | otherwise
  = Nothing


------------------------------------------------------------------------------
-------------------------------- A CoreBind Visitor --------------------------
------------------------------------------------------------------------------

-- TODO: syb-shrinkage

class CBVisitable a where
  freeVars :: S.HashSet Var -> a -> [Var]
  readVars :: a -> [Var] 
  letVars  :: a -> [Var] 
  literals :: a -> [Literal]

instance CBVisitable [CoreBind] where
  freeVars env cbs = (sortNub xs) \\ ys 
    where xs = concatMap (freeVars env) cbs 
          ys = concatMap bindings cbs
  
  readVars = concatMap readVars
  letVars  = concatMap letVars 
  literals = concatMap literals

instance CBVisitable CoreBind where
  freeVars env (NonRec x e) = freeVars (extendEnv env [x]) e 
  freeVars env (Rec xes)    = concatMap (freeVars env') es 
                              where (xs,es) = unzip xes 
                                    env'    = extendEnv env xs 

  readVars (NonRec _ e)     = readVars e
  readVars (Rec xes)        = concatMap readVars $ map snd xes

  letVars (NonRec x e)      = x : letVars e
  letVars (Rec xes)         = xs ++ concatMap letVars es
    where 
      (xs, es)              = unzip xes

  literals (NonRec _ e)      = literals e
  literals (Rec xes)         = concatMap literals $ map snd xes

instance CBVisitable (Expr Var) where
  freeVars = exprFreeVars
  readVars = exprReadVars
  letVars  = exprLetVars
  literals = exprLiterals

exprFreeVars = go 
  where 
    go env (Var x)         = if x `S.member` env then [] else [x]  
    go env (App e a)       = (go env e) ++ (go env a)
    go env (Lam x e)       = go (extendEnv env [x]) e
    go env (Let b e)       = (freeVars env b) ++ (go (extendEnv env (bindings b)) e)
    go env (Tick _ e)      = go env e
    go env (Cast e _)      = go env e
    go env (Case e x _ cs) = (go env e) ++ (concatMap (freeVars (extendEnv env [x])) cs) 
    go _   _               = []

exprReadVars = go
  where
    go (Var x)             = [x]
    go (App e a)           = concatMap go [e, a] 
    go (Lam _ e)           = go e
    go (Let b e)           = readVars b ++ go e 
    go (Tick _ e)          = go e
    go (Cast e _)          = go e
    go (Case e _ _ cs)     = (go e) ++ (concatMap readVars cs) 
    go _                   = []

exprLetVars = go
  where
    go (Var x)             = []
    go (App e a)           = concatMap go [e, a] 
    go (Lam x e)           = x : go e
    go (Let b e)           = letVars b ++ go e 
    go (Tick _ e)          = go e
    go (Cast e _)          = go e
    go (Case e x _ cs)     = x : go e ++ concatMap letVars cs
    go _                   = []

exprLiterals = go
  where
    go (Lit l)             = [l]
    go (App e a)           = concatMap go [e, a] 
    go (Let b e)           = literals b ++ go e 
    go (Lam _ e)           = go e
    go (Tick _ e)          = go e
    go (Cast e _)          = go e
    go (Case e _ _ cs)     = (go e) ++ (concatMap literals cs) 
    go _                   = []


instance CBVisitable (Alt Var) where
  freeVars env (a, xs, e) = freeVars env a ++ freeVars (extendEnv env xs) e
  readVars (_,_, e)       = readVars e
  letVars  (_,xs,e)       = xs ++ letVars e
  literals (c,_, e)       = literals c ++ literals e


instance CBVisitable AltCon where
  freeVars _ (DataAlt dc) = dataConImplicitIds dc
  freeVars _ _            = []
  readVars _              = []
  letVars  _              = []
  literals (LitAlt l)     = [l]
  literals _              = []


names     = (map varName) . bindings

extendEnv = foldl' (flip S.insert)

bindings (NonRec x _) 
  = [x]
bindings (Rec  xes  ) 
  = map fst xes

--------------------------------------------------------------------
------ Strictness --------------------------------------------------
--------------------------------------------------------------------

instance NFData Var
instance NFData SrcSpan



instance PPrint GhcSpec where
  pprint spec =  (text "******* Target Variables ********************")
              $$ (pprint $ tgtVars spec)
              $$ (text "******* Type Signatures *********************")
              $$ (pprintLongList $ tySigs spec)
              $$ (text "******* DataCon Specifications (Measure) ****")
              $$ (pprintLongList $ ctor spec)
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



pprintLongList = brackets . vcat . map pprint
