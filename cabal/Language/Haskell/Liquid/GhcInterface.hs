
{-# LANGUAGE NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, ScopedTypeVariables #-}

module Language.Haskell.Liquid.GhcInterface where

import GHC		
import Outputable
import HscTypes 
import CoreSyn
import Var
import IdInfo
import Name     (getSrcSpan)
import CoreMonad (liftIO)
import Serialized 
import Annotations 
import CorePrep
import VarEnv
import DataCon 
import HscMain
import TypeRep
import Module
import MonadUtils (concatMapM, mapSndM)
import qualified Control.Exception as Ex

import GHC.Paths (libdir)
import System.FilePath (dropFileName) 
import System.Directory (copyFile) 
import System.Environment (getArgs)
import DynFlags (defaultDynFlags)

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

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Haskell.HsColour.ACSS as ACSS
import qualified Language.Haskell.HsColour.CSS as CSS
import Debug.Trace

------------------------------------------------------------------
---------------------- GHC Bindings:  Code & Spec ----------------
------------------------------------------------------------------

--newtype Spec = Spec (VarEnv (Var, RefType))

data GhcInfo = GI { env      :: !HscEnv
                  , cbs      :: ![CoreBind]
                  , assm     :: ![(Var, RefType)]
                  , grty     :: ![(Var, RefType)]
                  , ctor     :: ![(Var, RefType)]
                  , meas     :: ![(Symbol, RefType)]
                  , hqFiles  :: ![FilePath]
                  , wiredIn  :: ![(Var, RefType)]
                  }

instance Outputable GhcInfo where 
  ppr info =  (text "*************** Core Bindings ***************")
           $$ (ppr $ cbs info)
           $$ (text "*************** Free Variables **************")
           $$ (ppr $ importVars $ cbs info)
           $$ (text "******* Bound-Annotations (Guarantee) *******")
           $$ (ppr $ grty info)
           $$ (text "******* Free-Annotations (Assume) ***********")
           $$ (ppr $ assm info)
           $$ (text "******DataCon Specifications (Measure) ******")
           $$ (ppr $ ctor info)
           $$ (text "******* Measure Specifications **************")
           $$ (ppr $ meas info)
           $$ (text "******* Builtin Specifications **************")
           $$ (ppr $ wiredIn info)
 
------------------------------------------------------------------
-------------- Extracting CoreBindings From File -----------------
------------------------------------------------------------------

updateDynFlags df ps 
  = df { importPaths = ps ++ importPaths df } 
       { libraryPaths = ps ++ libraryPaths df}

getGhcModGuts1 fn = do
   liftIO $ deleteBinFiles fn 
   target <- guessTarget fn Nothing
   addTarget target
   load LoadAllTargets
   modGraph <- depanal [] True
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       mod_guts <- coreModule `fmap` (desugarModule =<< typecheckModule =<< parseModule modSummary)
       return mod_guts

getGhcInfo target paths = 
    runGhc (Just libdir) $ do
      df  <- getSessionDynFlags
      setSessionDynFlags $ updateDynFlags df paths
      mg  <- getGhcModGuts1 target
      liftIO $ putStrLn "Raw CoreBinds" 
      liftIO $ putStrLn $ showPpr (mg_binds mg)
      env <- getSession

      cbs <- liftIO $ anormalize env mg
      -- guarantees for variables bound in this module
      grt <- varsSpec (mg_module mg) $ concatMap bindings cbs
      grt' <- moduleSpec' mg paths
      liftIO $ putStrLn "Guarantee Spec" 
      liftIO $ putStrLn $ showPpr (grt ++ grt')
       -- module specifications
      (ins, asm, msr) <- moduleSpec mg paths (importVars cbs) 
      -- module qualifiers 
      hqs  <- moduleHquals mg paths target ins 
      -- DEAD construct reftypes for wiredIns and such
      bs  <- wiredInSpec env 
      return $ GI env cbs asm (grt ++ grt') (fst msr) (snd msr) hqs bs

printVars s vs 
  = do putStrLn s 
       putStrLn $ showPpr [(v, getSrcSpan v) | v <- vs]

moduleHquals mg paths target imports 
  = do hqs   <- moduleAnnFiles Hquals paths (mg_module mg)
       hqs'  <- moduleImpFiles Hquals paths ((mg_namestring mg) : imports)
       let rv = nubSort $ hqs ++ hqs'
       liftIO $ putStrLn $ "Reading Qualifiers From: " ++ show rv 
       return rv

mg_namestring = moduleNameString . moduleName . mg_module

importVars = freeVars S.empty 


dataCons info = filter isDataCon (importVars $ cbs info)

dataConId v = 
 case (idDetails v) of
   DataConWorkId i -> i
   DataConWrapId i -> i
   _               -> errorstar "dataConId on non DataCon"

isDataCon v = 
 case (idDetails v) of
   DataConWorkId _ -> True
--   DataConWrapId _ -> True
   _               -> False

-----------------------------------------------------------------------------
---------- Extracting Refinement Type Specifications From Annots ------------
-----------------------------------------------------------------------------

varsSpec m vs 
  = do (xs,bs) <- (unzip . catMaybes) <$> mapM varAnnot vs
       setContext [IIModule m]
       env     <- getSession
       rs      <- liftIO $ mkRefTypes env bs 
       return   $ zip xs rs

varAnnot v 
  = do anns <- findGlobalAnns deserializeWithData $ NamedTarget $ varName v 
       case anns of 
         [a] -> return $ Just $ (v, rr' (varUniqueStr v) a)
         []  -> return $ Nothing 
         _   -> errorstar $ "Conflicting Spec-Annots for " ++ showPpr v

varUniqueStr :: Var -> String
varUniqueStr = show . varUnique
------------------------------------------------------------------------------------
------------ Extracting Specifications (Measures + Assumptions) --------------------
------------------------------------------------------------------------------------

--parseSpecs :: [FilePath] -> IO (Ms.Spec BareType Symbol) 
parseSpecs files 
  = liftIO $ liftM mconcat $ forM files $ \f -> 
      do putStrLn $ "parseSpec: " ++ f 
         Ex.catch (liftM (rr' f) $ readFile f{-rrWithFile $ f-}) $ \(e :: Ex.IOException) ->
           ioError $ userError $ "Hit exception: " ++ (show e) ++ " while parsing Spec file: " ++ f

moduleSpec' mg paths 
  = do myfs   <- moduleImpFiles Spec paths [mg_namestring mg]
       myspec <- parseSpecs myfs 
       env    <- getSession
       msr    <- liftIO $ mkMeasureSpec env $ Ms.mkMSpec (Ms.measures myspec)
       refspec <-liftIO $  mkAssumeSpec env (Ms.assumes myspec)
--       liftIO  $ putStrLn $ "Is this correct?: " ++ showPpr refspec 
       return  refspec
 
moduleSpec mg paths impVars 
  = do -- specs imported by me 
       fs     <- moduleImpFiles Spec paths impNames 
       spec   <- moduleSpecLoop paths S.empty mempty fs
       -- measures from me 
       myfs   <- moduleImpFiles Spec paths [mg_namestring mg]
       myspec <- parseSpecs myfs 
       -- all modules, including specs, imported by me
       let ins = nubSort $ impNames ++ [s | S s <- Ms.imports spec]
       liftIO  $ putStrLn $ "Module Imports: " ++ show ins 
       -- convert to GHC
       setContext [IIModule mod]
       env    <- getSession
       msr    <- liftIO $ mkMeasureSpec env $ Ms.mkMSpec (Ms.measures spec ++ Ms.measures myspec)
       xts    <- liftIO $ mkAssumeSpec env  $ Ms.assumes spec
       xts'   <- varsSpec mod impVars
       return  $ (ins, xts ++ xts', msr)
    where mod      = mg_module mg
          impNames = (moduleNameString . moduleName) <$> impMods
          impMods  = moduleEnvKeys $ mg_dir_imps mg

--moduleSpecLoop :: GhcMonad m => [FilePath] -> S.Set FilePath -> Ms.Spec BareType Symbol -> [FilePath] -> m (Ms.Spec BareType Symbol)
moduleSpecLoop _ _ spec []       
  = return spec
moduleSpecLoop paths seenFiles spec newFiles 
  = do newSpec   <- parseSpecs newFiles 
       impFiles  <- moduleImpFiles Spec paths [s | S s <- Ms.imports newSpec]
       let seenFiles' = seenFiles  `S.union` (S.fromList newFiles)
       let spec'      = spec `mappend` newSpec
       let newFiles'  = [f | f <- impFiles, f `S.notMember` seenFiles']
       moduleSpecLoop paths seenFiles' spec' newFiles'

moduleImpFiles ext paths names 
  = liftIO $ liftM catMaybes $ forM extNames (namePath paths)
    where extNames = (`extModuleName` ext) <$> names 

--moduleImpSpecFiles :: GhcMonad m => [FilePath] -> [String] -> m [FilePath]
--moduleImpSpecFiles = paths impNames 
--  = liftIO $ liftM catMaybes $ forM extNames (namePath paths)
--    where extNames = (`extModuleName` Spec) <$> impNames
  
namePath paths name 
  = do res <- getFileInDirs name paths
       case res of
         Just p  -> putStrLn $ "namePath: name = " ++ name ++ " expanded to: " ++ (show p) 
         Nothing -> putStrLn $ "namePath: name = " ++ name ++ " not found in: " ++ (show paths)
       return res

moduleAnnFiles :: GhcMonad m => Ext -> [FilePath] -> Module -> m [FilePath]
moduleAnnFiles ext paths mod
  = do reqs  <- (findGlobalAnns deserializeWithData $ ModuleTarget mod)
       let libFile  = extFileName ext preludeName
       let incFiles = catMaybes $ reqFile ext <$> reqs 
       liftIO $ forM (libFile : incFiles) (`findFileInDirs` paths)

reqFile ext s 
  | isExtFile ext s 
  = Just s 
  | otherwise
  = Nothing

-------------------------------------------------------------------------
------------ Builtins Refinement Type Specifications --------------------
-------------------------------------------------------------------------

wiredInSpec _ = return []

--wiredInSpec_ env 
--  = do vs <- liftIO $ mkIds env ns 
--       return $ wiredIns ++ (zip vs ts)
--    where (ns, ts) = unzip nameds
--     
--nameds   :: [(Name, RefType)]
--nameds   = [] -- (smallIntegerName, ..?)
--
--wiredIns :: [(Var, RefType)]
--wiredIns 
--  = [( dataConWorkId intDataCon
--    , RFun bx (tcon0 intPrimTyCon trueReft) (tcon0 intTyCon $ symbolReft x))
--    ]
--    where x       = S "x"
--          bx      = RB x
--          tcon0 c = RCon (typeId c) (RPrimTyCon c) [] 



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

  -- where xd = case x of 
  -- Nothing -> text "unknown"
  -- Just v  -> ppr v

applySolution :: FixSolution -> AnnInfo RefType -> AnnInfo RefType
applySolution = fmap . fmap . mapReft . map . appSolRefa  
  where appSolRefa _ ra@(RConc _) = ra 
        appSolRefa s (RKvar k su) = RConc $ subst su $ M.findWithDefault PTop k s  
        mapReft f (Reft (x, zs)) = Reft (x, f zs)

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
  freeVars env (Case e _ _ cs) = (freeVars env e) ++ (concatMap (freeVars env) cs) 
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

instance NFData GhcInfo where
  rnf (GI x1 x2 x3 x4 x5 x6 x7 x8) 
    = {-# SCC "NFGhcInfo" #-} x1 `seq` x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` rnf x8

