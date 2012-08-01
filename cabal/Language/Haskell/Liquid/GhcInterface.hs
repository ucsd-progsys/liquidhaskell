
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables #-}

module Language.Haskell.Liquid.GhcInterface where

import GHC 
import Outputable
import HscTypes
import CoreSyn
import Var
import TysWiredIn
import BasicTypes (TupleSort(BoxedTuple), Arity)
import IdInfo
import Name     (getSrcSpan)
import CoreMonad (liftIO)
import Serialized
import Annotations
import CorePrep
import VarEnv
import DataCon
import TyCon
import qualified TyCon as TC
import HscMain
import TypeRep
import Module
import Language.Haskell.Liquid.Desugar.HscMain (hscDesugarWithLoc) 
import MonadUtils (concatMapM, mapSndM)
import qualified Control.Exception as Ex

import GHC.Paths (libdir)
import System.FilePath (dropExtension, takeFileName, dropFileName) 
import System.Directory (copyFile) 
import System.Environment (getArgs)
import DynFlags (defaultDynFlags, ProfAuto(..))
import Control.Monad (filterM)
import Control.Arrow hiding ((<+>))
import Control.DeepSeq
import Control.Applicative  hiding (empty)
import Control.Monad (forM_, forM, liftM, (>=>))
import Data.Data
import Data.Monoid hiding ((<>))
import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf, foldl', nub, find, (\\))
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Exts         (groupWith, sortWith)
import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)

import Language.Haskell.Liquid.Fixpoint hiding (Expr) 
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.ANFTransform
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.PredType

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Haskell.HsColour.ACSS as ACSS
import qualified Language.Haskell.HsColour.CSS as CSS
-- import Debug.Trace

------------------------------------------------------------------
---------------------- GHC Bindings:  Code & Spec ----------------
------------------------------------------------------------------

data GhcSpec = SP {
    imports    :: ![String]
  , tySigs     :: ![(Var, SpecType)]
  , ctor       :: ![(Var, RefType)]
  , meas       :: ![(Symbol, RefType)]
  , dconsP     :: ![(DataCon, DataConP)]
  , tconsP     :: ![(TC.TyCon, TyConP)]
  , includes   :: ![FilePath]
  , invariants :: ![SpecType]
  }

data GhcInfo = GI { 
    env      :: !HscEnv
  , cbs      :: ![CoreBind]
  , impVars  :: ![Var]
  , defVars  :: ![Var]
  , hqFiles  :: ![FilePath]
  , spec     :: !GhcSpec
  }

instance Outputable GhcSpec where
  ppr spec =  (text "******* Imports *****************************")
           $$ (ppr $ imports spec)
           $$ (text "******* Type Signatures *********************")
           $$ (ppr $ tySigs spec)
           $$ (text "******* DataCon Specifications (Measure) ****")
           $$ (ppr $ ctor spec)
           $$ (text "******* Measure Specifications **************")
           $$ (ppr $ meas spec)
           $$ (text "******* Include Files *********************")
           $$ (ppr $ includes spec)

instance Outputable GhcInfo where 
  ppr info =  (text "*************** Core Bindings ***************")
           $$ (ppr $ cbs info)
           $$ (text "*************** Imported Variables **********")
           $$ (ppr $ impVars info)
           $$ (text "*************** Defined Variables ***********")
           $$ (ppr $ defVars info)
           $$ (text "*************** Specification ***************")
           $$ (ppr $ spec info)

instance Show GhcInfo where
  show = showPpr 

------------------------------------------------------------------
-------------- Extracting CoreBindings From File -----------------
------------------------------------------------------------------

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
       return mod_guts

getGhcInfo target paths 
  = runGhc (Just libdir) $ do
      df          <- getSessionDynFlags
      setSessionDynFlags $ updateDynFlags df paths
      modguts     <- getGhcModGuts1 target
      hscEnv      <- getSession
      -- modguts     <- liftIO $ hscSimplify hscEnv modguts
      coreBinds   <- liftIO $ anormalize hscEnv modguts
      spec        <- moduleSpec target modguts paths 
      liftIO       $ putStrLn $ "Module Imports: " ++ show (imports spec) 
      hqualFiles  <- moduleHquals modguts paths target spec 
      return       $ GI hscEnv coreBinds (importVars coreBinds) (definedVars coreBinds) hqualFiles spec 

moduleHquals mg paths target spec
  = do hqs   <- specIncludes Hquals paths (includes spec)
       hqs'  <- moduleImports Hquals paths ((mg_namestring mg) : (imports spec))
       let rv = nubSort $ hqs ++ (snd <$> hqs')
       liftIO $ putStrLn $ "Reading Qualifiers From: " ++ show rv 
       return rv

printVars s vs 
  = do putStrLn s 
       putStrLn $ showPpr [(v, getSrcSpan v) | v <- vs]

mg_namestring = moduleNameString . moduleName . mg_module

importVars  = freeVars S.empty 
definedVars = concatMap defs 
  where defs (NonRec x _) = [x]
        defs (Rec xes)    = map fst xes


instance Show TC.TyCon where
 show = showSDoc . ppr

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
 
moduleSpec target mg paths
  = do liftIO      $ putStrLn ("paths = " ++ show paths) 
       spec1      <- getSpecs Spec paths impNames 
       spec2      <- getSpecs Hs   paths impNames 
       let spec    = mconcat [spec1, spec2]
       setContext [IIModule (mg_module mg)]
       env        <- getSession
       (cs, ms)   <- liftIO $ mkMeasureSpec env $ Ms.mkMSpec $ Ms.measures   spec
       tySigs     <- liftIO $ mkAssumeSpec  env              $ Ms.sigs       spec
       (tcs, dcs) <- liftIO $ mkConTypes    env              $ Ms.dataDecls  spec 
       invs       <- liftIO $ mkInvariants  env              $ Ms.invariants spec 
       return $ SP { imports    = nubSort $ impNames ++ [symbolString x | x <- Ms.imports spec]
                   , tySigs     = tySigs
                   , ctor       = cs
                   , meas       = ms
                   , dconsP     = {- traceShow "dconsP:" $ -} concat dcs ++ snd wiredTyDataCons 
                   , tconsP     = {- traceShow "tconsP:" $ -} tcs ++ fst wiredTyDataCons 
                   , includes   = Ms.includes spec
                   , invariants = invs
                   }
    where impNames = allDepNames target mg

allDepNames target mg = traceShow "allDepNames" $ allNames'
  where allNames'     = nubSort $ (targetName target) : (mg_namestring mg) : impNames
        impNames      = moduleNameString <$> (depNames mg ++ dirImportNames mg) 

depNames       = map fst        . dep_mods      . mg_deps
dirImportNames = map moduleName . moduleEnvKeys . mg_dir_imps  
targetName     = dropExtension  . takeFileName 

getSpecs ext paths names 
  = do fs <- moduleImports ext paths names 
       liftIO $ putStrLn ("getSpecs: " ++ show fs)
       transParseSpecs ext paths S.empty mempty fs

transParseSpecs _ _ _ spec []       
  = return spec
transParseSpecs ext paths seenFiles spec newFiles 
  = do liftIO $ putStrLn ("txParseSpecs: " ++ show newFiles)
       newSpec   <- liftIO $ liftM mconcat $ mapM (parseSpec ext) newFiles 
       impFiles  <- moduleImports ext paths [symbolString x | x <- Ms.imports newSpec]
       let seenFiles' = seenFiles  `S.union` (S.fromList newFiles)
       let spec'      = spec `mappend` newSpec
       let newFiles'  = [f | f <- impFiles, f `S.notMember` seenFiles']
       transParseSpecs ext paths seenFiles' spec' newFiles'
 
parseSpec ext (name, file) 
  = Ex.catch (parseSpec' ext name file) $ \(e :: Ex.IOException) ->
      ioError $ userError $ "Hit exception: " ++ (show e) ++ " while parsing Spec file: " ++ file ++ " for module " ++ name 


parseSpec' ext name file 
  = do putStrLn $ "parseSpec: " ++ file ++ " for module " ++ name  
       str     <- readFile file
       let spec = specParser ext name file str
       return   $ spec 

specParser Spec _  = rr'
specParser Hs name = hsSpecificationP name

moduleImports ext paths = liftIO . liftM catMaybes . mapM (mnamePath paths ext) 
mnamePath paths ext name = fmap (name,) <$> getFileInDirs fileName paths
  where fileName = name `extModuleName` ext


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

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

newtype AnnInfo a 
  = AI (M.Map SrcSpan (Maybe Var, a))
    deriving (Data, Typeable)

type Annot 
  = Either RefType SrcSpan
    -- deriving (Data, Typeable)

instance Functor AnnInfo where
  fmap f (AI m) = AI (fmap (\(x, y) -> (x, f y)) m)

instance Outputable a => Outputable (AnnInfo a) where
  ppr (AI m) = vcat $ map pprAnnInfoBind $ M.toList m 
 

pprAnnInfoBind (RealSrcSpan k, xv) 
  = xd $$ ppr l $$ ppr c $$ ppr n $$ vd $$ text "\n\n\n"
    where l        = srcSpanStartLine k
          c        = srcSpanStartCol k
          (xd, vd) = pprXOT xv 
          n        = length $ lines $ showSDoc vd

pprAnnInfoBind (_, _) 
  = empty

pprXOT (x, v) = (xd, ppr v)
  where xd = maybe (text "unknown") ppr x

applySolution :: FixSolution -> AnnInfo RefType -> AnnInfo RefType
applySolution = fmap . fmap . mapReft . map . appSolRefa  
  where appSolRefa _ ra@(RConc _) = ra 
        appSolRefa _ p@(RPvar _)  = p  
        appSolRefa s (RKvar k su) = RConc $ subst su $ M.findWithDefault PTop k s  
        mapReft f (Reft (x, zs))  = Reft (x, squishRas $ f zs)

squishRas ras  = (squish [p | RConc p <- ras]) : [ra | ra@(RPvar _) <- ras]
  where squish = RConc . pAnd . nubSort . filter (not . isTautoPred) . concatMap conjuncts   

conjuncts (PAnd ps)          = concatMap conjuncts ps
conjuncts p | isTautoPred p  = []
            | otherwise      = [p]


-------------------------------------------------------------------
------------------- Rendering Inferred Types ----------------------
-------------------------------------------------------------------

annotate :: FilePath -> FixSolution -> AnnInfo Annot -> IO ()
annotate fname sol anna 
  = do annotDump fname (extFileName Html $ extFileName Cst fname) annm
       annotDump fname (extFileName Html fname) annm'
    where annm = closeAnnots anna
          annm' = tidyRefType <$> applySolution sol annm

annotDump :: FilePath -> FilePath -> AnnInfo RefType -> IO ()
annotDump srcFile htmlFile ann 
  = do src <- readFile srcFile
       -- generate html
       let body = {-# SCC "hsannot" #-} ACSS.hsannot False (src, mkAnnMap ann)
       writeFile htmlFile $ CSS.top'n'tail srcFile $! body
       -- generate .annot
       copyFile srcFile annotFile
       appendFile annotFile $ show annm
    where annotFile = extFileName Annot srcFile
          annm      = mkAnnMap ann

mkAnnMap :: AnnInfo RefType -> ACSS.AnnMap
mkAnnMap (AI m) 
  = ACSS.Ann 
  $ M.fromList
  $ map (srcSpanLoc *** bindString)
  $ map (head . sortWith (srcSpanEndCol . fst)) 
  $ groupWith (lineCol . fst) 
  $ [ (l, m) | (RealSrcSpan l, m) <- M.toList m, oneLine l]  
  where bindString = mapPair (showSDocForUser neverQualify) . pprXOT 

srcSpanLoc l 
  = ACSS.L (srcSpanStartLine l, srcSpanStartCol l)
oneLine l  
  = srcSpanStartLine l == srcSpanEndLine l
lineCol l  
  = (srcSpanStartLine l, srcSpanStartCol l)

closeAnnots :: AnnInfo Annot -> AnnInfo RefType
closeAnnots = closeA . filterA
  
closeA a@(AI m)  = cf <$> a 
  where cf (Right loc) = case m `mlookup` loc of
                           (_, Left t) -> t
                           _           -> errorstar $ "malformed AnnInfo: " ++ showPpr loc
        cf (Left t)    = t

filterA (AI m) = AI (M.filter ff m)
  where ff (_, Right loc) = loc `M.member` m
        ff _              = True
        
--instance Show SrcSpan where
--  show = showPpr




------------------------------------------------------------------------------
-------------------------------- A CoreBind Visitor --------------------------
------------------------------------------------------------------------------

-- TODO: syb-shrinkage

class CBVisitable a where
  freeVars :: S.Set Var -> a -> [Var]
  readVars :: a -> [Var] 

instance CBVisitable [CoreBind] where
  freeVars env cbs = (nubSort xs) \\ ys 
    where xs = concatMap (freeVars env) cbs 
          ys = concatMap bindings cbs
  
  readVars cbs = concatMap readVars cbs  

instance CBVisitable CoreBind where
  freeVars env (NonRec x e) = freeVars (extendEnv env [x]) e 
  freeVars env (Rec xes)    = concatMap (freeVars env') es 
                              where (xs,es) = unzip xes 
                                    env'    = extendEnv env xs 

  readVars (NonRec x e)      = readVars e
  readVars (Rec xes)         = concatMap readVars $ map snd xes

instance CBVisitable (Expr Var) where
  freeVars env (Var x)         = if x `S.member` env then [] else [x]  
  freeVars env (App e a)       = (freeVars env e) ++ (freeVars env a)
  freeVars env (Lam x e)       = freeVars (extendEnv env [x]) e
  freeVars env (Let b e)       = (freeVars env b) ++ (freeVars (extendEnv env (bindings b)) e)
  freeVars env (Tick _ e)      = freeVars env e
  freeVars env (Cast e _)      = freeVars env e
  freeVars env (Case e x _ cs) = (freeVars env e) ++ (concatMap (freeVars (extendEnv env [x])) cs) 
  freeVars env (Lit _)         = []
  freeVars env (Type _)	       = []

  readVars (Var x)             = [x]
  readVars (App e a)           = concatMap readVars [e, a] 
  readVars (Lam x e)           = readVars e
  readVars (Let b e)           = readVars b ++ readVars e 
  readVars (Tick _ e)          = readVars e
  readVars (Cast e _)          = readVars e
  readVars (Case e _ _ cs)     = (readVars e) ++ (concatMap readVars cs) 
  readVars (Lit _)             = []
  readVars (Type _)	           = []


instance CBVisitable (Alt Var) where
  freeVars env (a, xs, e) = freeVars env a ++ freeVars (extendEnv env xs) e
  readVars (_,_, e)       = readVars e

instance CBVisitable AltCon where
  freeVars _ (DataAlt dc) = [dataConWorkId dc]
  freeVars _ _            = []
  readVars _              = []


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

ppFreeVars    = showSDoc . vcat .  map ppFreeVar 
ppFreeVar x   = ppr n <> text " :: " <> ppr t <> text "\n" 
                where n = varName x
                      t = varType x

ppVarExp (x,e) = text "Var " <> ppr x <> text " := " <> ppr e
ppBlank = text "\n_____________________________\n"

--------------------------------------------------------------------
------ Strictness --------------------------------------------------
--------------------------------------------------------------------

instance NFData Var
instance NFData SrcSpan
instance NFData a => NFData (AnnInfo a) where
  rnf (AI x) = () -- rnf x

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

--------------------------------------------------------------------
------ Predicate Types for WiredIns --------------------------------
--------------------------------------------------------------------

maxArity :: Arity 
maxArity = 7

wiredTyDataCons :: ([(TC.TyCon, TyConP)] , [(DataCon, DataConP)])
wiredTyDataCons = (\(x, y) -> (concat x, concat y)) $ unzip l
  where l = [listTyDataCons] ++ map tupleTyDataCons [1..maxArity] 

listTyDataCons :: ([(TC.TyCon, TyConP)] , [(DataCon, DataConP)])
listTyDataCons = ( [(c, TyConP [(RTV tyv)] [p])]
                 , [(nilDataCon , DataConP [(RTV tyv)] [p] [] lt)
                 , (consDataCon, DataConP [(RTV tyv)] [p]  cargs  lt)])
    where c     = listTyCon
          [tyv] = tyConTyVars c
          t     = TyVarTy tyv
          fld   = stringSymbol "fld"
          x     = stringSymbol "x"
          xs    = stringSymbol "xs"
          p     = PV (stringSymbol "p") t [(t, fld, fld)]
          px    = pdVar $ PV (stringSymbol "p") t [(t, fld, x)]
          lt    = rApp c [xt] [RMono $ pdVar p] pdTrue 
          xt    = RVar (RV (RTV tyv)) pdTrue
          xst   = rApp c [RVar (RV (RTV tyv)) px] [RMono $ pdVar p] pdTrue
          cargs = [(xs, xst), (x, xt)]

tupleTyDataCons :: Int -> ([(TC.TyCon, TyConP)] , [(DataCon, DataConP)])
tupleTyDataCons n = ( [(c, TyConP (RTV <$> tyv) ps)]
                    , [(dc, DataConP (RTV <$> tyv) ps  cargs  lt)])
  where c       = tupleTyCon BoxedTuple n
        dc      = tupleCon BoxedTuple n 
        tyv     = tyConTyVars c
        (ta:ts) = TyVarTy <$>tyv
        tvs     = tyv
        flds    = mks "fld"
        fld     = stringSymbol "fld"
        x1:xs   = mks "x"
        y       = stringSymbol "y"
        ps      = mkps pnames (ta:ts) ((fld,fld):(zip flds flds))
        pxs     = mkps pnames (ta:ts) ((fld, x1):(zip flds xs))
        lt      = rApp c ((\x -> RVar (RV (RTV x)) pdTrue) <$> tyv) 
                         (RMono . pdVar <$> ps) pdTrue 
        xts     = zipWith (\v p -> RVar (RV (RTV v))(pdVar p)) 
                          (tail tvs) pxs
        cargs   = reverse $ (x1, RVar (RV (RTV (head tvs))) pdTrue)
                            :(zip xs xts)
        pnames  = mks_ "p"
        mks  x  = (\i -> stringSymbol (x++ show i)) <$> [1..n]
        mks_ x  = (\i ->  (x++ show i)) <$> [2..n]


mkps ns (t:ts) ((f,x):fxs) = reverse $ mkps_ (stringSymbol <$> ns) ts fxs [(t, f, x)] [] 

mkps_ []     _       _          _    ps = ps
mkps_ (n:ns) (t:ts) ((f, x):xs) args ps
  = mkps_ ns ts xs (a:args) (p:ps)
  where p = PV n t args
        a = (t, f, x)
