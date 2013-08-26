{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module Language.Haskell.Liquid.GhcMisc where

import           Debug.Trace

import           Kind                         (superKind)
import           CoreSyn                      hiding (Expr)
import           CostCentre
import           FamInstEnv                   (FamInst)
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           SrcLoc                       (srcSpanFile, srcSpanStartLine, srcSpanStartCol)

import           Language.Fixpoint.Misc       (errorstar, stripParens)
import           Text.Parsec.Pos              (sourceName, sourceLine, sourceColumn, SourcePos, newPos) 
import           Language.Fixpoint.Types      hiding (SESearch(..))
import           Name                         (mkInternalName, getSrcSpan)
import           OccName                      (mkTyVarOcc, mkTcOcc)
import           Unique                       
import           Finder                       (findImportedModule, cannotFindModule)
import           DynamicLoading
import           ErrUtils
import           Exception
import           Panic                        (GhcException(..), throwGhcException)
import           RnNames                      (gresFromAvails)
import           HscMain
import           HscTypes                     (HscEnv(..), FindResult(..), ModIface(..), lookupTypeHscEnv)
import           FastString
import           TcRnDriver
import           OccName


import           RdrName
import           Type                         (liftedTypeKind)
import           TypeRep                       
import           Var
-- import           TyCon                        (mkSuperKindTyCon)
import qualified TyCon                        as TC
import qualified DataCon                      as DC
import           FastString                   (uniq, unpackFS, fsLit)
import           Data.Char                    (isLower, isSpace)
import           Data.Maybe
import           Data.Hashable
import qualified Data.HashSet                 as S    
import qualified Data.List                    as L    
import           Control.Applicative          ((<$>))
import           Control.Arrow                (second)
import           Control.Exception            (assert, throw)
import           Outputable                   (Outputable (..), text, ppr)
import qualified Outputable                   as Out
import           DynFlags
-- import           Language.Haskell.Liquid.Types

-- import qualified Pretty                       as P
import qualified Text.PrettyPrint.HughesPJ    as PJ

-----------------------------------------------------------------------
--------------- Datatype For Holding GHC ModGuts ----------------------
-----------------------------------------------------------------------

data MGIModGuts = MI {
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: !ImportedMods
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  }

miModGuts mg = MI {
    mgi_binds     = mg_binds mg
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mg_dir_imps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  }

-----------------------------------------------------------------------
--------------- Generic Helpers for Encoding Location -----------------
-----------------------------------------------------------------------

srcSpanTick :: Module -> SrcSpan -> Tickish a
srcSpanTick m loc
  = ProfNote (AllCafsCC m loc) False True

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote (AllCafsCC _ loc) _ _)
  = loc
tickSrcSpan z
  = errorstar $ "tickSrcSpan: unhandled tick: " ++ showPpr z

-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
        occ  = mkTcOcc s

stringTyCon :: Char -> Int -> String -> TyCon
stringTyCon c n s = TC.mkKindTyCon name superKind
  where 
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTyVarOcc $ assert (validTyVar s) s

hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (FunTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType _               = False
validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && all (not . isSpace) s 
validTyVar _       = False

tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} showPpr α ++ show (varUnique α)

tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow = text . show


tidyCBs = map unTick

unTick (NonRec b e) = NonRec b (unTickExpr e)
unTick (Rec bs)     = Rec $ map (second unTickExpr) bs

unTickExpr (App e a)          = App (unTickExpr e) (unTickExpr a)
unTickExpr (Lam b e)          = Lam b (unTickExpr e)
unTickExpr (Let b e)          = Let (unTick b) (unTickExpr e)
unTickExpr (Case e b t as)    = Case (unTickExpr e) b t (map unTickAlt as)
    where unTickAlt (a, b, e) = (a, b, unTickExpr e)
unTickExpr (Cast e c)         = Cast (unTickExpr e) c
unTickExpr (Tick _ e)         = unTickExpr e
unTickExpr x                  = x

-----------------------------------------------------------------------
------------------ Generic Helpers for DataConstructors ---------------
-----------------------------------------------------------------------

getDataConVarUnique v
  | isId v && isDataConWorkId v = getUnique $ idDataCon v
  | otherwise                   = getUnique v
  

newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

instance Hashable Loc where
  hashWithSalt i (L z) = hashWithSalt i z 

--instance (Uniquable a) => Hashable a where

instance Hashable SrcSpan where
  hashWithSalt i (UnhelpfulSpan s) = hashWithSalt i (uniq s) 
  hashWithSalt i (RealSrcSpan s)   = hashWithSalt i (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

instance Outputable a => Outputable (S.HashSet a) where
  ppr = ppr . S.toList 

-------------------------------------------------------

toFixSDoc = PJ.text . PJ.render . toFix 
sDocDoc   = PJ.text . showSDoc 
pprDoc    = sDocDoc . ppr

-- Overriding Outputable functions because they now require DynFlags!
showPpr      = Out.showPpr tracingDynFlags
showSDoc     = Out.showSDoc tracingDynFlags
showSDocDump = Out.showSDocDump tracingDynFlags

typeUniqueString = {- ("sort_" ++) . -} showSDocDump . ppr

instance Fixpoint Var where
  toFix = pprDoc 

instance Fixpoint Name where
  toFix = pprDoc 

instance Fixpoint Type where
  toFix = pprDoc


sourcePosSrcSpan   :: SourcePos -> SrcSpan
sourcePosSrcSpan = srcLocSpan . sourcePosSrcLoc 

sourcePosSrcLoc    :: SourcePos -> SrcLoc
sourcePosSrcLoc p = mkSrcLoc (fsLit file) line col  
  where 
    file          = sourceName p
    line          = sourceLine p
    col           = sourceColumn p

srcSpanSourcePos :: SrcSpan -> SourcePos
srcSpanSourcePos (UnhelpfulSpan _) = dummyPos 
srcSpanSourcePos (RealSrcSpan s)   = realSrcSpanSourcePos s

srcSpanStartLoc l  = L (srcSpanStartLine l, srcSpanStartCol l)
srcSpanEndLoc l    = L (srcSpanEndLine l, srcSpanEndCol l)
oneLine l          = srcSpanStartLine l == srcSpanEndLine l
lineCol l          = (srcSpanStartLine l, srcSpanStartCol l)
dummyPos :: SourcePos
dummyPos = newPos "?" 0 0 

realSrcSpanSourcePos :: RealSrcSpan -> SourcePos 
realSrcSpanSourcePos s = newPos file line col
  where 
    file               = unpackFS $ srcSpanFile s
    line               = srcSpanStartLine       s
    col                = srcSpanStartCol        s

getSourcePos           = srcSpanSourcePos . getSrcSpan 


collectArguments n e = if length xs > n then take n xs else xs
  where (vs', e') = collectValBinders' $ snd $ collectTyBinders e
        vs        = fst $ collectValBinders $ ignoreLetBinds e'
        xs        = vs' ++ vs

collectValBinders' expr = go [] expr
  where
    go tvs (Lam b e) | isTyVar b = go tvs     e
    go tvs (Lam b e) | isId    b = go (b:tvs) e
    go tvs e                     = (reverse tvs, e)

ignoreLetBinds e@(Let (NonRec x xe) e') 
  = ignoreLetBinds e'
ignoreLetBinds e 
  = e

isDictionary x = L.isPrefixOf "$d" (showPpr x)
isInternal   x = L.isPrefixOf "$" (showPpr x)


instance Hashable Var where
  hashWithSalt = uniqueHash 

instance Hashable TyCon where
  hashWithSalt = uniqueHash 

uniqueHash i = hashWithSalt i . getKey . getUnique

-- slightly modified version of DynamicLoading.lookupRdrNameInModule
lookupRdrName :: HscEnv -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrName hsc_env mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Find the exports of the module
            (_, mb_iface) <- getModuleInterface hsc_env mod
            case mb_iface of
                Just iface -> do
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
                        provenance = Imported [ImpSpec decl_spec ImpAll]
                        env = case mi_globals iface of
                                Nothing -> mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                                Just e -> e
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> Out.panic "lookupRdrNameInModule"
                Nothing -> throwCmdLineErrorS dflags $ Out.hsep [Out.ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where dflags = hsc_dflags hsc_env
        throwCmdLineErrorS dflags = throwCmdLineError . Out.showSDoc dflags
        throwCmdLineError = throwGhcException . CmdLineError


addContext m = getContext >>= setContext . (m:)

qualImportDecl mn = (simpleImportDecl mn) { ideclQualified = True }
