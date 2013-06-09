{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

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
import           Text.Parsec.Pos              (SourcePos, newPos) 
import           Language.Fixpoint.Types       
import           Language.Haskell.Liquid.Types 
import           Name                         (mkInternalName, getSrcSpan)
import           OccName                      (mkTyVarOcc, mkTcOcc)
import           Unique                       

import           RdrName                      (GlobalRdrEnv)
import           Type                         (liftedTypeKind)
import           TypeRep                       
import           Var
-- import           TyCon                        (mkSuperKindTyCon)
import qualified TyCon                        as TC
import qualified DataCon                      as DC
import           FastString                   (uniq, unpackFS)
import           Data.Char                    (isLower, isSpace)
import           Data.Maybe
import           Data.Hashable
import qualified Data.HashSet                 as S    
import qualified Data.List                    as L    
import           Control.Applicative          ((<$>))
import           Control.Arrow                (second)
import           Control.Exception            (assert)
import           Outputable                   (Outputable (..), text, ppr)
import qualified Outputable                   as Out
import           DynFlags
import           Language.Haskell.Liquid.Types

-- import qualified Pretty                       as P
import qualified Text.PrettyPrint.HughesPJ    as PJ

defaultTyConInfo = TyConInfo [] [] [] [] Nothing

mkTyConInfo :: TyCon -> [Int] -> [Int] -> (Maybe (Symbol -> Expr)) -> TyConInfo
mkTyConInfo c
  = TyConInfo [i | (i, b) <- varsigns, b, i /= dindex]
              [i | (i, b) <- varsigns, not b, i /= dindex]
  where varsigns  = L.nub $ concatMap goDCon $ TC.tyConDataCons c
        initmap   = zip (showPpr <$> tyvars) [0..]
        mkmap vs  = zip (showPpr <$> vs) (repeat (dindex)) ++ initmap
        goDCon dc = concatMap (go (mkmap (DC.dataConExTyVars dc)) True)
                              (DC.dataConOrigArgTys dc)
        go m pos (ForAllTy v t)  = go ((showPpr v, dindex):m) pos t
        go m pos (TyVarTy v)     = [(varLookup (showPpr v) m, pos)]
        go m pos (AppTy t1 t2)   = go m pos t1 ++ go m pos t2
        go m pos (TyConApp _ ts) = concatMap (go m pos) ts
        go m pos (FunTy t1 t2)   = go m (not pos) t1 ++ go m pos t2

        varLookup v m = fromMaybe (errmsg v) $ L.lookup v m
        tyvars        = TC.tyConTyVars c
        errmsg v      = error $ "GhcMisc.getTyConInfo: var not found" ++ showPpr v
        dindex        = -1

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
instance Hashable Var where
  hashWithSalt = uniqueHash 

instance Hashable TyCon where
  hashWithSalt = uniqueHash 

instance Hashable SrcSpan where
  hashWithSalt i (UnhelpfulSpan s) = hashWithSalt i (uniq s) 
  hashWithSalt i (RealSrcSpan s)   = hashWithSalt i (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

uniqueHash i = hashWithSalt i . getKey . getUnique

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


srcSpanSourcePos :: SrcSpan -> SourcePos
srcSpanSourcePos (UnhelpfulSpan _) = dummyPos 
srcSpanSourcePos (RealSrcSpan s)   = realSrcSpanSourcePos s

realSrcSpanSourcePos :: RealSrcSpan -> SourcePos 
realSrcSpanSourcePos s = newPos file line col
  where 
    file               = unpackFS $ srcSpanFile s
    line               = srcSpanStartLine       s
    col                = srcSpanStartCol        s

getSourcePos           = srcSpanSourcePos . getSrcSpan 

