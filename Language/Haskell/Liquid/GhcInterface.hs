
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables #-}

module Language.Haskell.Liquid.GhcInterface where

import GHC 
import Outputable   (showPpr)
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
import System.FilePath (dropExtension, takeFileName) 


import DynFlags (ProfAuto(..))
import Control.Monad (filterM)
import Control.DeepSeq
import Control.Applicative  hiding (empty)
import Control.Monad (forM, liftM)
import Data.Monoid hiding ((<>))
import Data.List (intercalate, foldl', find, (\\))
import Data.Maybe (catMaybes)
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import System.Directory (doesFileExist)
import Language.Fixpoint.Types hiding (Expr) 
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.ANFTransform
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GhcMisc

import Language.Haskell.Liquid.Parse
import Language.Fixpoint.Parse
import Language.Fixpoint.Names
import Language.Fixpoint.Files

import qualified Language.Haskell.Liquid.Measure as Ms


------------------------------------------------------------------
---------------------- GHC Bindings:  Code & Spec ----------------
------------------------------------------------------------------


data GhcInfo = GI { 
    env      :: !HscEnv
  , cbs      :: ![CoreBind]
  , impVars  :: ![Var]
  , defVars  :: ![Var]
  , hqFiles  :: ![FilePath]
  , imports  :: ![String]
  , includes :: ![FilePath]
  , spec     :: !GhcSpec
  }

instance Fixpoint GhcSpec where
  toFix spec =  (text "******* Type Signatures *********************")
             $$ (toFix $ tySigs spec)
             $$ (text "******* DataCon Specifications (Measure) ****")
             $$ (toFix $ ctor spec)
             $$ (text "******* Measure Specifications **************")
             $$ (toFix $ meas spec)

instance Fixpoint GhcInfo where 
  toFix info =  (text "*************** Imports *********************")
             $$ (pprDoc $ imports info)
             $$ (text "*************** Includes ********************")
             $$ (pprDoc $ includes info)
             $$ (text "*************** Core Bindings ***************")
             $$ (pprDoc $ cbs info)
             $$ (text "*************** Imported Variables **********")
             $$ (pprDoc $ impVars info)
             $$ (text "*************** Defined Variables ***********")
             $$ (pprDoc $ defVars info)
             $$ (text "*************** Specification ***************")
             $$ (toFix $ spec info)

instance Show GhcInfo where
  show = showFix

------------------------------------------------------------------
-------------- Extracting CoreBindings From File -----------------
------------------------------------------------------------------

--- {{{
--- compileCore :: GhcMonad m => Bool -> FilePath -> m CoreModule
--- compileCore simplify fn = do
---    -- First, set the target to the desired filename
---    target <- guessTarget fn Nothing
---    addTarget target
---    _ <- load LoadAllTargets
---    -- Then find dependencies
---    modGraph <- depanal [] True
---    case find ((== fn) . msHsFilePath) modGraph of
---      Just modSummary -> do
---        -- Now we have the module name;
---        -- parse, typecheck and desugar the module
---        mod_guts <- coreModule `fmap`
---                       -- TODO: space leaky: call hsc* directly?
---                       (desugarModule =<< typecheckModule =<< parseModule modSummary)
---        liftM (gutsToCoreModule (mg_safe_haskell mod_guts)) $
---          if simplify
---           then do
---              -- If simplify is true: simplify (hscSimplify), then tidy (tidyProgram).
---              hsc_env <- getSession
---              simpl_guts <- liftIO $ hscSimplify hsc_env mod_guts
---              tidy_guts <- liftIO $ tidyProgram hsc_env simpl_guts
---              return $ Left tidy_guts
---           else
---              return $ Right mod_guts
--- 
---      Nothing -> panic "compileToCoreModule: target FilePath not found in\
---                            module dependency graph"
---   where -- two versions, based on whether we simplify (thus run tidyProgram,
---         -- which returns a (CgGuts, ModDetails) pair, or not (in which case
---         -- we just have a ModGuts.
---         gutsToCoreModule :: SafeHaskellMode
---                          -> Either (CgGuts, ModDetails) ModGuts
---                          -> CoreModule
---         gutsToCoreModule safe_mode (Left (cg, md)) = CoreModule {
---           cm_module = cg_module cg,
---           cm_types  = md_types md,
---           cm_binds  = cg_binds cg,
---           cm_safe   = safe_mode
---         }
---         gutsToCoreModule safe_mode (Right mg) = CoreModule {
---           cm_module  = mg_module mg,
---           cm_types   = typeEnvFromEntities (bindersOfBinds (mg_binds mg))
---                                            (mg_tcs mg)
---                                            (mg_fam_insts mg),
---           cm_binds   = mg_binds mg,
---           cm_safe    = safe_mode
---          }
--- }}}

updateDynFlags df ps 
  = df { importPaths  = ps ++ importPaths df  } 
       { libraryPaths = ps ++ libraryPaths df }
       { profAuto     = ProfAutoCalls         }

getGhcModGuts1 fn = do
   liftIO $ deleteBinFiles fn 
   target <- guessTarget fn Nothing
   addTarget target
   load LoadAllTargets
   modGraph <- depanal [] True
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       mod_guts <- coreModule `fmap` (desugarModuleWithLoc =<< typecheckModule =<< parseModule modSummary)
       return   $! (miModGuts mod_guts)
     Nothing         -> error "GhcInterface : getGhcModGuts1"

-- Generates Simplified ModGuts (INLINED, etc.) but without SrcSpan
getGhcModGutsSimpl1 fn = do
   liftIO $ deleteBinFiles fn 
   target <- guessTarget fn Nothing
   addTarget target
   load LoadAllTargets
   modGraph <- depanal [] True
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

getGhcInfo target paths 
  = runGhc (Just libdir) $ do
      df                 <- getSessionDynFlags
      setSessionDynFlags  $ updateDynFlags df paths
      -- peepGHCSimple target 
      modguts            <- getGhcModGuts1 target
      hscEnv             <- getSession
      -- modguts     <- liftIO $ hscSimplify hscEnv modguts
      coreBinds          <- liftIO $ anormalize hscEnv modguts
      let impvs           = importVars coreBinds 
      let defvs           = definedVars coreBinds 
      (spec, imps, incs) <- moduleSpec (impvs ++ defvs) target modguts paths 
      liftIO              $ putStrLn $ "Module Imports: " ++ show imps 
      hqualFiles         <- moduleHquals modguts paths target imps incs 
      return              $ GI hscEnv coreBinds impvs defvs hqualFiles imps incs spec 

moduleHquals mg paths target imps incs 
  = do hqs   <- specIncludes Hquals paths incs 
       hqs'  <- moduleImports [Hquals] paths (mgi_namestring mg : imps)
       hqs'' <- liftIO $ filterM doesFileExist [extFileName Hquals target]
       let rv = sortNub $ hqs'' ++ hqs ++ (snd <$> hqs')
       liftIO $ putStrLn $ "Reading Qualifiers From: " ++ show rv 
       return rv

printVars s vs 
  = do putStrLn s 
       putStrLn $ showPpr [(v, getSrcSpan v) | v <- vs]

mgi_namestring = moduleNameString . moduleName . mgi_module

importVars  = freeVars S.empty 
definedVars = concatMap defs 
  where defs (NonRec x _) = [x]
        defs (Rec xes)    = map fst xes

-- instance Show TC.TyCon where
--   show = showPpr 

--------------------------------------------------------------------------------
---------------------------- Desugaring (Taken from GHC) -----------------------
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
--------------- Extracting Specifications (Measures + Assumptions) -------------
--------------------------------------------------------------------------------
 
moduleSpec vars target mg paths
  = do liftIO      $ putStrLn ("paths = " ++ show paths) 
       tgtSpec    <- liftIO $ parseSpec (name, target) 
       _          <- liftIO $ checkAssertSpec vars             $ Ms.sigs       tgtSpec
       impSpec    <- getSpecs paths impNames [Spec, Hs, LHs] 
       let spec    = Ms.expandRTAliases $ tgtSpec `mappend` impSpec 
       let imps    = sortNub $ impNames ++ [symbolString x | x <- Ms.imports spec]
       setContext [IIModule (mgi_module mg)]
       env        <- getSession
       ghcSpec    <- liftIO $ makeGhcSpec vars env spec
       return      (ghcSpec, imps, Ms.includes tgtSpec)
    where impNames = allDepNames  mg
          name     = mgi_namestring mg

allDepNames mg    = allNames'
  where allNames' = sortNub impNames
        impNames  = moduleNameString <$> (depNames mg ++ dirImportNames mg) 

depNames       = map fst        . dep_mods      . mgi_deps
dirImportNames = map moduleName . moduleEnvKeys . mgi_dir_imps  
targetName     = dropExtension  . takeFileName 

getSpecs paths names exts
  = do fs    <- sortNub <$> moduleImports exts paths names 
       liftIO $ putStrLn ("getSpecs: " ++ show fs)
       transParseSpecs exts paths S.empty mempty fs

transParseSpecs _ _ _ spec []       
  = return spec
transParseSpecs exts paths seenFiles spec newFiles 
  = do newSpec   <- liftIO $ liftM mconcat $ mapM parseSpec newFiles 
       impFiles  <- moduleImports exts paths [symbolString x | x <- Ms.imports newSpec]
       let seenFiles' = seenFiles  `S.union` (S.fromList newFiles)
       let spec'      = spec `mappend` newSpec
       let newFiles'  = [f | f <- impFiles, not (f `S.member` seenFiles')]
       transParseSpecs exts paths seenFiles' spec' newFiles'
 
parseSpec (name, file) 
  = Ex.catch (parseSpec' name file) $ \(e :: Ex.IOException) ->
      ioError $ userError $ "Hit exception: " ++ (show e) ++ " while parsing Spec file: " ++ file ++ " for module " ++ name 


parseSpec' name file 
  = do putStrLn $ "parseSpec: " ++ file ++ " for module " ++ name  
       str     <- readFile file
       let spec = specParser name file str
       return   $ spec 

specParser name file str  
  | isExtFile Spec file  = rr' file str
  | isExtFile Hs file    = hsSpecificationP name file str
  | isExtFile LHs file   = hsSpecificationP name file str
  | otherwise            = errorstar $ "specParser: Cannot Parse File " ++ file

--specParser Spec _  = rr'
--specParser Hs name = hsSpecificationP name

--moduleImports ext paths  = liftIO . liftM catMaybes . mapM (mnamePath paths ext) 
--mnamePath paths ext name = fmap (name,) <$> getFileInDirs file paths
--                           where file = name `extModuleName` ext

moduleImports exts paths 
  = liftIO . liftM concat . mapM (moduleFiles paths exts) 

moduleFiles paths exts name 
  = do files <- mapM (`getFileInDirs` paths) (extModuleName name <$> exts)
       return [(name, file) | Just file <- files]


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

checkAssertSpec :: [Var] -> [(Symbol, BareType)] -> IO () 
checkAssertSpec vs xbs =
  let vm  = M.fromList [(showPpr v, v) | v <- vs] 
      xs' = [s | (x, _) <- xbs, let s = symbolString x, not (M.member s vm)]
  in case xs' of 
    [] -> return () 
    _  -> errorstar $ "Asserts for Unknown variables: "  ++ (intercalate ", " xs')  


------------------------------------------------------------------------------
-------------------------------- A CoreBind Visitor --------------------------
------------------------------------------------------------------------------

-- TODO: syb-shrinkage

class CBVisitable a where
  freeVars :: S.HashSet Var -> a -> [Var]
  readVars :: a -> [Var] 
  literals :: a -> [Literal]

instance CBVisitable [CoreBind] where
  freeVars env cbs = (sortNub xs) \\ ys 
    where xs = concatMap (freeVars env) cbs 
          ys = concatMap bindings cbs
  
  readVars cbs = concatMap readVars cbs  
  literals cbs = concatMap literals cbs

instance CBVisitable CoreBind where
  freeVars env (NonRec x e) = freeVars (extendEnv env [x]) e 
  freeVars env (Rec xes)    = concatMap (freeVars env') es 
                              where (xs,es) = unzip xes 
                                    env'    = extendEnv env xs 

  readVars (NonRec _ e)      = readVars e
  readVars (Rec xes)         = concatMap readVars $ map snd xes

  literals (NonRec _ e)      = literals e
  literals (Rec xes)         = concatMap literals $ map snd xes

instance CBVisitable (Expr Var) where
  freeVars = exprFreeVars
  readVars = exprReadVars
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
  literals (c,_, e)       = literals c ++ literals e


instance CBVisitable AltCon where
  freeVars _ (DataAlt dc) = dataConImplicitIds dc
  freeVars _ _            = []
  readVars _              = []
  literals (LitAlt l)     = [l]
  literals _              = []


names     = (map varName) . bindings

extendEnv = foldl' (flip S.insert)

bindings (NonRec x _) 
  = [x]
bindings (Rec  xes  ) 
  = map fst xes

---------------------------------------------------------------
------------------ Printing Related Functions -----------------
---------------------------------------------------------------

--instance Outputable Spec where
--  ppr (Spec s) = vcat $ map pprAnnot $ varEnvElts s 
--    where pprAnnot (x,r) = ppr x <> text " @@ " <> ppr r <> text "\n"

-- ppFreeVars    = showSDoc . vcat .  map ppFreeVar 
-- ppFreeVar x   = pprDoc n <> text " :: " <> pprDoc t <> text "\n" 
--                 where n = varName x
--                       t = varType x

-- ppVarExp (x,e) = text "Var " <> pprDoc x <> text " := " <> pprDoc e
-- ppBlank = text "\n_____________________________\n"

--------------------------------------------------------------------
------ Strictness --------------------------------------------------
--------------------------------------------------------------------

instance NFData Var
instance NFData SrcSpan

--instance NFData GhcInfo where
--  rnf (GI x1 x2 x3 x4 x5 x6 x7 x8 _ _ _) 
--    = {-# SCC "NFGhcInfo" #-} 
--      x1 `seq` 
--      x2 `seq` 
--      {- rnf -} x3 `seq` 
--      {- rnf -} x4 `seq` 
--      {- rnf -} x5 `seq` 
--      {- rnf -} x6 `seq` 
--      {- rnf -} x7 `seq` 
--      {- rnf -} x8


