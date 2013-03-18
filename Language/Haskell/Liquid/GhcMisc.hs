{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.Haskell.Liquid.GhcMisc where
import           Kind                         (superKind)
import           CoreSyn
import           CostCentre
import           FamInstEnv                   (FamInst)
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           Language.Fixpoint.Misc       (errorstar, stripParens)
import           Language.Fixpoint.Types       
import           Name                         (mkInternalName)
import           OccName                      (mkTyVarOcc, mkTcOcc)
import           Unique                       

import           RdrName                      (GlobalRdrEnv)
import           Type                         (liftedTypeKind)
import           TypeRep                       
import           Var
-- import           TyCon                        (mkSuperKindTyCon)
import qualified TyCon                        as TC
import qualified DataCon                      as DC
import           FastString                   (uniq)
import           Data.Char                    (isLower, isSpace)
import           Data.Maybe
import           Data.Hashable
import qualified Data.HashSet                 as S    
import qualified Data.List                    as L    
import           Control.Applicative          ((<$>))
import           Control.Exception            (assert)
import           Outputable

-- import qualified Pretty                       as P
import qualified Text.PrettyPrint.HughesPJ    as PJ


-----------------------------------------------------------------------
----------- TyCon get CoVariance - ContraVariance Info ----------------
-----------------------------------------------------------------------

data TyConInfo = TyConInfo
  { covariantTyArgs     :: ![Int] -- indexes of covariant type arguments
  , contravariantTyArgs :: ![Int] -- indexes of contravariant type arguments
  , covariantPsArgs     :: ![Int] -- indexes of covariant predicate arguments
  , contravariantPsArgs :: ![Int] -- indexes of contravariant predicate arguments
  }

-- indexes start from 0 and type or predicate arguments can be both
-- covariant and contravaariant
-- eg, for the below Foo dataType
-- data Foo a b c <p :: b -> Prop, q :: Int -> Prop, r :: a -> Prop>
--   = F (a<r> -> b<p>) | Q (c -> a) | G (Int<q> -> a<r>)
-- there will be 
--  covariantTyArgs     = [0, 1], for type arguments a and b
--  contravariantTyArgs = [0, 2], for type arguments a and c
--  covariantPsArgs     = [0, 2], for predicate arguments p and r
--  contravariantPsArgs = [1, 2], for predicate arguments q and r

defaultTyConInfo = TyConInfo [] [] [] []

mkTyConInfo :: TyCon -> [Int] -> [Int]-> TyConInfo
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
  = errorstar $ "tickSrcSpan: unhandled tick" ++ showPpr z

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

tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} show α ++ show (varUnique α)


tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow = text . show

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

--------------------------------------------------------------------------------

-- pjDocToGHCDoc = go
--   where 
--     go (PJ.Empty)             = P.Empty
--     go (PJ.NilAbove d)        = P.NilAbove (go d) 
--     go (PJ.TextBeside td i d) = P.TextBeside (goTD td) i (go d)   
--     go (PJ.Nest i d)          = P.Nest i (go d) 
--     go (PJ.Union d1 d2)       = P.Union (go d1) (go d2)
--     go (PJ.NoDoc)             = P.NoDoc
--     go (PJ.Beside d1 b d2)    = P.Beside (go d1) b (go d2)           
--     go (PJ.Above d1 b d2)     = P.Above (go d1) b (go d2)
-- 
--     goTD (PJ.Chr c)           = P.Chr c
--     goTD (PJ.Str s)           = P.Str s
--     goTD (PJ.PStr s)          = P.PStr s
-- 
-- ghcDocToPJDoc = go
--   where 
--     go (P.Empty)             = PJ.Empty
--     go (P.NilAbove d)        = PJ.NilAbove (go d) 
--     go (P.TextBeside td i d) = PJ.TextBeside (goTD td) i (go d)   
--     go (P.Nest i d)          = PJ.Nest i (go d) 
--     go (P.Union d1 d2)       = PJ.Union (go d1) (go d2)
--     go (P.NoDoc)             = PJ.NoDoc
--     go (P.Beside d1 b d2)    = PJ.Beside (go d1) b (go d2)           
--     go (P.Above d1 b d2)     = PJ.Above (go d1) b (go d2)
-- 
--     goTD (P.Chr c)           = PJ.Chr c
--     goTD (P.Str s)           = PJ.Str s
--     goTD (P.PStr s)          = PJ.PStr s

-- instance Fixpoint a => Outputable a where 
--   ppr = docToSDoc . pjDocToGHCDoc . toFix 

-- instance Fixpoint a => Outputable a where 
--   ppr = text . PJ.render . toFix 

toFixSDoc = text . PJ.render . toFix 
sDocDoc   = PJ.text . showSDoc 
pprDoc    = sDocDoc . ppr 

typeUniqueString = {- ("sort_" ++) . -} showSDocDump . ppr


instance Fixpoint Var where
  toFix = pprDoc 

instance Fixpoint Name where
  toFix = pprDoc 

instance Fixpoint Type where
  toFix = pprDoc

