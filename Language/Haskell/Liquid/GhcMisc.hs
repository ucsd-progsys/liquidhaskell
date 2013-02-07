{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Haskell.Liquid.GhcMisc where

import           CoreSyn
import           CostCentre
import           FamInstEnv                   (FamInst)
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           Language.Fixpoint.Misc (errorstar, stripParens)
import           Name                         (mkInternalName)
import           OccName                      (mkTyVarOcc, mkTcOcc)
import           Unique                       
import           Outputable
import           RdrName                      (GlobalRdrEnv)
import           Type                         (liftedTypeKind)
import           TypeRep                       
import           Var
import           TyCon                        (mkSuperKindTyCon)
import qualified TyCon                        as TC
import qualified DataCon                      as DC
import           FastString                   (uniq)
-- import           SrcLoc                       hiding (L)
import           Data.Char                    (isLower, isSpace)
import           Data.Maybe
import           Data.Hashable
import qualified Data.HashSet                 as S    
import qualified Data.List                    as L    
import           Control.Applicative          ((<$>))
import           Control.Exception            (assert)

-----------------------------------------------------------------------
----------- TyCon get CoVariiance - ContraVariance Info ---------------
-----------------------------------------------------------------------
data TyConInfo = TyConInfo
  { covariantTyArgs     :: ![Int]
  , contravariantTyArgs :: ![Int]
  , covariantPsArgs     :: ![Int]
  , contravariantPsArgs :: ![Int]
  }

defaultTyConInfo = TyConInfo [] [] [] []

mkTyConInfo :: TyCon -> [Int] -> [Int]-> TyConInfo
mkTyConInfo c
  = TyConInfo [i | (i,  b) <- varsigns, b, i>=0]
              [i | (i, b) <- varsigns, not b, i>=0]
  where varsigns = L.nub $ concatMap (go initmap True) tys
        initmap  = zip (showPpr <$> tyvars) [0..]
        tys = [ ty | dc <- TC.tyConDataCons c
                   , ty <- DC.dataConRepArgTys dc]
        go m pos (ForAllTy v t)  = go ((showPpr m, -1):m) pos t
        go m pos (TyVarTy v)     = [(varLookup (showPpr v) m, pos)]
        go m pos (AppTy t1 t2)   = go m pos t1 ++ go m pos t2
        go m pos (TyConApp _ ts) = concatMap (go m pos) ts
        go m pos (FunTy t1 t2)   = go m (not pos) t1 ++ go m pos t2

        varLookup v m = fromMaybe (errmsg v) $ L.lookup v m
        tyvars        = TC.tyConTyVars c
        errmsg v      = error $ "GhcMisc.getTyConInfo: var not found" ++ showPpr v -- , ty, zip tyvars [(1 :: Int)..])

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
  = errorstar $ "tickSrcSpan: unhandled tick" ++ showPpr z

-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
        occ  = mkTcOcc s

stringTyCon :: Char -> Int -> String -> TyCon
stringTyCon c n s = mkSuperKindTyCon name
  where name = mkInternalName (mkUnique c n) occ noSrcSpan
        occ  = mkTyVarOcc $ assert (validTyVar s) s

hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (FunTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType _               = False
validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && all (not . isSpace) s 
validTyVar _       = False

tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} show α ++ show (varUnique α)

intersperse d ds = hsep $ punctuate (space <> d) ds

tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow = text . show

-- dropModuleNames [] = []
-- dropModuleNames s  = last $ words $ dotWhite <$> stripParens s
--   where dotWhite '.' = ' '
--         dotWhite c   = c


-----------------------------------------------------------------------
------------------ Generic Helpers for DataConstructors ---------------
-----------------------------------------------------------------------

getDataConVarUnique v
  | isId v && isDataConWorkId v = getUnique $ idDataCon v
  | otherwise                   = getUnique v
  

newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

instance Hashable Loc where
  hash (L z) = hash z 

--instance (Uniquable a) => Hashable a where
instance Hashable Var where
  hash = uniqueHash 

instance Hashable TyCon where
  hash = uniqueHash 

instance Hashable SrcSpan where
  hash (UnhelpfulSpan s) = hash (uniq s) 
  hash (RealSrcSpan s)   = hash (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

uniqueHash = hash . getKey . getUnique

instance Outputable a => Outputable (S.HashSet a) where
  ppr = ppr . S.toList 




