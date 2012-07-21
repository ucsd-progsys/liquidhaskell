{-# LANGUAGE IncoherentInstances, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}

{- Refinement Types Mirroring the GHC Type definition -}

module Language.Haskell.Liquid.RefType (
    RTyVar (..), RType (..), RRType (..), BRType (..), RTyCon(..)
  , TyConable (..), Reftable(..), RefTypable (..), SubsTy (..), Ref(..)
  , RefType, PrType, BareType, SpecType
  , Predicate (..), UReft(..), DataDecl (..)
  , pdAnd, pdVar, pdTrue, pvars
  , Bind (..), RBind
  , ppr_rtype, mapReft, mapBind
  , ofType, ofPredTree, toType
  , rTyVar, rVar, rApp, rFun
  , typeUniqueSymbol
  , strengthen -- , strengthenRefType
  , generalize, mkArrow, normalizePds, rsplitVsPs, rsplitArgsRes
  , subts, substSym 
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, refTypePredSortedReft, refTypeSortedReft, typeSortedReft, rTypeSort, funcToObj
  -- , canonRefType
  , tidyRefType
  , mkSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalConst
  , REnv, deleteREnv, domREnv, insertREnv, lookupREnv, emptyREnv, memberREnv, fromListREnv
  , addTyConInfo
  , primOrderingSort
  , fromRMono, fromRPoly, idRMono
  ) where

import Text.Printf
import Control.Exception.Base
import Control.Exception (assert)
import GHC
import Outputable
import qualified TyCon as TC
import DataCon
import TypeRep 
import Type (expandTypeSynonyms)

import Var
import VarEnv
import PrelNames
import Name             (getSrcSpan, getOccString, mkInternalName)
import Unique           (getUnique)
import Literal
import Type             (isPredTy, mkTyConTy, liftedTypeKind, substTyWith, classifyPredType, PredTree(..), predTreePredType)
-- import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon, eqDataCon, ltDataCon, gtDataCon)

import Data.Monoid      hiding ((<>))
import Data.Maybe               (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S 
import Control.Applicative  hiding (empty)   
import Data.Bifunctor
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq
import qualified Data.Foldable as Fold

import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc (tvId, stringTyVar, intersperse, dropModuleNames)
import Language.Haskell.Liquid.FileNames (listConName, tupConName, boolConName)
import Data.List (sort, isPrefixOf, isSuffixOf, find, foldl')

--------------------------------------------------------------------
------------------ Predicate Variables -----------------------------
--------------------------------------------------------------------

{- moved to Fixpoint.hs -}
{-
data PVar t
  = PV { pname :: !Symbol
       , ptype :: !t
       , pargs :: ![(t, Symbol, Symbol)]
       }
	deriving (Data, Typeable, Show)

instance Eq (PVar t) where
  pv == pv' = (pname pv == pname pv') {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _)  (PV n' _ _) = compare n n'

instance Functor PVar where
  fmap f (PV x t txys) = PV x (f t) (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t txys) = rnf n `seq` rnf t `seq` rnf txys

--instance Subable (PVar a) where
--  subst su (PV p t args) = PV p t $ [(t, x, subst su y) | (t, x, y) <- args]
--
--instance MapSymbol (PVar a) where 
--  mapSymbol f (PV p t args) = PV (f p) t [(t, x, f y) | (t, x, y) <- args]
-}
--------------------------------------------------------------------
------------------ Predicates --------------------------------------
--------------------------------------------------------------------

newtype Predicate t = Pr [PVar t] deriving (Data, Typeable)

pdTrue         = Pr []
pdVar v        = Pr [v]
pvars (Pr pvs) = pvs
pdAnd ps       = Pr (concatMap pvars ps)

-- UNIFY: Why?!
instance Eq (Predicate a) where
  (==) = eqpd

eqpd (Pr vs) (Pr ws) 
  = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
    where vs' = sort vs
          ws' = sort ws

instance Functor Predicate where
  fmap f (Pr pvs) = Pr (fmap f <$> pvs)

instance Monoid (Predicate t) where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Outputable (PVar t)) => Outputable (Predicate t) where
  ppr (Pr [])       = text "True"
  ppr (Pr pvs)      = hsep $ punctuate (text "&") (map ppr pvs)

instance Outputable (Predicate t) => Show (Predicate t) where
  show = showPpr 

instance Outputable (PVar t) => Reftable (Predicate t) where
  isTauto (Pr ps) 
    = null ps
  ppTy r d 
    | isTauto r = d 
    | otherwise = d <> (angleBrackets $ ppr r)
  

instance NFData (Predicate a) where
  rnf _ = ()

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()

--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------

data Bind tv pv = RB Symbol | RV tv | RP pv 
  deriving (Data, Typeable)

{- INVARIANTS:
 measure isTyVarBind :: Bind tv pv -> Bool
 isTyVarBind (RV _) = true 
 isTyVarBind (RP _) = false
 isTyVarBind (RB _) = false
-}

data RType p c tv pv r
  = RVar !(Bind tv pv) !r                                            -- INV: RVar {v | isTyVarBind v}
  | RFun !(Bind tv pv) !(RType p c tv pv r) !(RType p c tv pv r) !r  -- INV: RFun {v | isSymBind v} t1 t2
  | RAll !(Bind tv pv) !(RType p c tv pv r)                          -- INV: RAll {v | !(isSymBind v) }
  | RApp !c ![(RType p c tv pv r)] ![Ref r (RType p c tv pv r)] !r
  | RCls !p ![(RType p c tv pv r)]
  | ROth String
  deriving (Data, Typeable)

data Ref s m = RMono s | RPoly m
  deriving (Data, Typeable)

type BRType     = RType String String String   
type RRType     = RType Class  RTyCon RTyVar   

data UReft r t  = U {ureft :: !r, upred :: !(Predicate t)}
                  deriving (Data, Typeable)

type BareType   = BRType (PVar String) (UReft Reft String) 
type SpecType   = RRType (PVar Type)   (UReft Reft Type)
type PrType     = RRType (PVar Type)   (Predicate Type) 
type RefType    = RRType (PVar Type)   Reft

data DataDecl   = D String 
                    [String] 
                    [PVar String] 
                    [(String, [(String, BareType)])] 
                  deriving (Data, Typeable, Show)

class (Monoid r, Outputable r) => Reftable r where 
  isTauto :: r -> Bool
  ppTy    :: r -> SDoc -> SDoc
  
  top     :: r
  top     =  mempty
  
  meet    :: r -> r -> r
  meet    = mappend

fromRMono :: String -> Ref a b -> a
fromRMono m (RMono r) = r
fromRMono m _        = error $ "fromMono" ++ m
fromRPoly (RPoly r) = r
fromRPoly _        = error "fromPoly"


idRMono = RMono . (fromRMono "idRMono")

class TyConable c where
  isList   :: c -> Bool
  isTuple  :: c -> Bool

class Outputable pv => PVarable pv where
  ppr_def :: pv -> SDoc

class (Outputable p, Outputable c, Outputable tv, PVarable pv, Reftable r, TyConable c, Subable r) => RefTypable p c tv pv r where
  ppCls    :: p -> [RType p c tv pv r] -> SDoc
  
  ppRType  :: Prec -> RType p c tv pv r -> SDoc 
  ppRType = ppr_rtype 



--------------------------------------------------------------------
---------------- Refinement Types: RefType -------------------------
--------------------------------------------------------------------

newtype RTyVar = RTV TyVar deriving (Data, Typeable)

instance Eq RTyVar where
  RTV α == RTV α' = tvId α == tvId α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = compare (tvId α) (tvId α')

type RBind = Bind RTyVar (PVar Type)

data RTyCon = RTyCon 
  { rTyCon     :: !TC.TyCon         -- GHC Type Constructor
  , rTyConPs   :: ![PVar Type]      -- Predicate Parameters
  }
  deriving (Eq, Data, Typeable)

instance Eq RBind where
  RB s == RB s' = s == s'
  RV α == RV α' = α == α'
  RP p == RP p' = pname p == pname p'
  _    == _     = False 

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rFun b t t'         = RFun b t t' top
rVar                = RVar . rTyVar 
rTyVar              = RV . RTV

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred p t = RAll (RP p) t
rApp c    = RApp (RTyCon c []) 


addPds ps (RAll v@(RV _) t) = RAll v $ addPds ps t
addPds ps t                 = foldl' (flip rPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2 r) 
 = (RFun b t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAll (RV v) t )
 = (RAll (RV v) t', ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(RApp c ts rs r)
 = (t, ps)
nlzP ps t@(RCls c ts)
 = (t, ps)
nlzP ps (RAll (RP p) t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(ROth _)
 = (t, ps)

strengthenRefType :: RefType -> RefType -> RefType
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = errorstar $ "strengthen on differently shaped reftypes! " 
              ++ "t1 = " ++ showPpr t1 
              ++ "t2 = " ++ showPpr t2
  where eqt t1 t2 = showPpr (toType t1) == showPpr (toType t2)
  
strengthenRefType_ (RAll a@(RV _) t1) (RAll _ t2)
  = RAll a $ strengthenRefType_ t1 t2

strengthenRefType_ (RFun (RB x1) t1 t1' r1) (RFun (RB x2) t2 t2' r2) 
  = RFun (RB x1) t t' (r1 `meet` r2)
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts = zipWith strengthenRefType_ t1s t2s
          rs = zipWith meet rs1 rs2

strengthenRefType_ (RVar v1 r1)  (RVar v2 r2)
  = RVar v1 (r1 `meet` r2)

strengthenRefType_ t1 _ 
  = t1

strengthen (RApp c ts rs r) r' = RApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'       = RVar a       (r `meet` r') 
strengthen (RFun b t1 t2 r) r' = RFun b t1 t2 (r `meet` r')
strengthen t _                 = t 


replaceReft (RApp c ts rs _) r' = RApp c ts rs r' 
replaceReft (RVar a _) r'      = RVar a      r' 
replaceReft t _                = t 


addTyConInfo :: (PVarable pv) => M.Map TC.TyCon RTyCon -> RRType pv Reft -> RRType pv Reft
addTyConInfo = mapBot . addTCI
addTCI tyi t@(RApp c ts rs r)
  = case (M.lookup (rTyCon c) tyi) of
     Just c' -> rConApp c' ts rs r
     Nothing -> rConApp c  ts rs r
addTCI _ t
  = t

showTy v = showSDoc $ ppr v <> ppr (varUnique v)
-- showTy t = showSDoc $ ppr t

rConApp (RTyCon c ps) ts rs r = RApp (RTyCon c ps') ts rs' r 
   where τs   = toType <$> ts
         ps'  = subts (zip cts τs) <$> ps
         cts  = RTV <$> TC.tyConTyVars c
         rs'  = if (null rs) 
                 then (RPoly . ofType . ptype <$> ps') 
                 else zipWith toPoly rs (ptype <$> ps')

toPoly (RPoly t) _ = RPoly t
toPoly (RMono r) t = RPoly $ (ofType t) `strengthen` r  

-- mkArrow ::  [TyVar] -> [(Symbol, RType a)] -> RType a -> RType a
mkArrow as xts t = mkUnivs as $ mkArrs xts t

mkUnivs αs t     = foldr RAll t $ (RV <$> αs)

mkArrs xts t     = foldr (\(x, t) -> rFun (RB x) t) t xts 



-- bkArrow :: RType a -> ([TyVar], [(Symbol, RType a)],  RType a)
bkArrow ty = (αs, xts, out)
  where (αs, t)    = bkUniv [] ty
        (xts, out) = bkArrs [] t
       

bkUniv αs (RAll (RV α) t) = bkUniv (α : αs) t
bkUniv αs t               = (reverse αs, t)

bkArrs xts (RFun (RB x) t t' _ ) = bkArrs ((x,t):xts) t'
bkArrs xts t                     = (reverse xts, t)

rsplitVsPs (RAll (RV v) t) = (v:vs, ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs (RAll (RP p) t) = (vs, p:ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs t = ([], [], t)

rsplitArgsRes (RFun (RB x) t1 t2 _) = (x:xs, t1:ts, r)
  where (xs, ts, r) = rsplitArgsRes t2
rsplitArgsRes t = ([], [], t)


-- generalize ::  Ord tv => RType p c tv pv r -> RType p c tv pv r
generalize t = mkUnivs αs t 
  where αs = S.toList $ freeVars t
         
freeVars (RAll (RP _) t) = freeVars t
freeVars (RAll (RV α) t) = S.delete α $ freeVars t
freeVars (RFun x t t' _) = S.unions   $ freeVars <$> [t, t']  
freeVars (RApp _ ts _ _) = S.unions   $ freeVars <$> ts
freeVars (RCls _ ts)     = S.unions   $ freeVars <$> ts 
freeVars (RVar (RV α) _) = S.singleton α 

----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData REnv where
  rnf (REnv m) = () -- rnf m

instance NFData (Bind a b) where
  rnf (RB x) = rnf x
  rnf (RV a) = ()
  rnf (RP p) = () 

instance (NFData a, NFData b) => NFData (Ref a b) where
  rnf (RMono a) = rnf a
  rnf (RPoly b) = rnf b

instance (NFData a, NFData b, NFData c, NFData d, NFData e) => NFData (RType a b c d e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAll α t)       = rnf α `seq` rnf t
  rnf (RFun x t t' r)  = rnf x `seq` rnf t `seq` rnf t' `seq` rnf r
  rnf (RApp c ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RCls c ts)      = c `seq` rnf ts
  rnf (ROth _)         = ()

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

ppr_tyvar = text . tvId

instance Outputable RTyVar where
  ppr (RTV α) = ppr_tyvar α 

instance Show RTyVar where
  show = showPpr 

instance Reftable (RType Class RTyCon RTyVar (PVar Type) Reft) where
  isTauto t = isTautoTy t
  ppTy      = error "ppTy RPoly Reftable" 


instance Reftable (Ref Reft (RType Class RTyCon RTyVar (PVar Type) Reft)) where
  isTauto (RMono r) = isTauto r
  isTauto (RPoly t) = isTauto t

  ppTy (RMono r) = ppTy r
  ppTy (RPoly t) = ppTy t

instance (Reftable r, RefTypable p c tv pv r, Subable r) => Reftable (Ref r (RType p c tv pv r)) where
  isTauto (RMono r) = isTauto r
  isTauto (RPoly p) = False

  ppTy (RMono r) d = ppTy r d
  ppTy (RPoly _) _ = error "Reftable r"


-- DEBUG ONLY
instance Outputable (Bind String (PVar String)) where
  ppr (RB x) = ppr x
  ppr (RV a) = text a
  ppr (RP p) = ppr p
 
instance (Outputable tv, Outputable pv) => Outputable (Bind tv pv) where
  ppr (RB x) = ppr x
  ppr (RV a) = ppr a
  ppr (RP p) = ppr p

instance Outputable (Bind tv pv) => Show (Bind tv pv) where
  show = showPpr 

instance (Reftable s, Outputable p) => Outputable (Ref s p) where
  ppr (RMono s) = ppr s
  ppr (RPoly p) = ppr p

instance TyConable RTyCon where
  isList  = (listTyCon ==) . rTyCon
  isTuple = TC.isTupleTyCon   . rTyCon 
 
instance Reftable Reft where
  isTauto = isTautoReft
  ppTy    = ppr_reft

instance TyConable String where
  isList  = (listConName ==) 
  isTuple = (tupConName ==)

instance (PVarable pv, Reftable r, Subable r) => RefTypable String String String pv r where
  ppCls c ts = parens (text c <+> text "...")

instance (Reftable r, Reftable (Predicate t)) => Outputable (UReft r t) where
  ppr (U r p)
    | isTauto r  = ppr p
    | isTauto p  = ppr r
    | otherwise  = ppr p <> text " & " <> ppr r

instance Outputable (UReft r t) => Show (UReft r t) where
  show = showSDoc . ppr 

instance (Monoid a) => Monoid (UReft a b) where
  mempty                    = U mempty mempty
  mappend (U x y) (U x' y') = U (mappend x x') (mappend y y')

instance Monoid RefType where
  mempty  = error "mempty RefType"
  mappend = strengthenRefType

instance Monoid (Ref Reft RefType) where
  mempty  = RMono mempty
  mappend (RMono r1) (RMono r2) = RMono $ r1 `meet` r2
  mappend (RMono r) (RPoly t)   = RPoly $ t `strengthen` r
  mappend (RPoly t) (RMono r)   = RPoly $ t `strengthen` r
  mappend (RPoly t1) (RPoly t2) = RPoly $ t1 `strengthenRefType` t2

instance (Monoid r, Reftable r, Subable r, RefTypable a b c d r) => Monoid (Ref r (RType a b c d r)) where
  mempty = RMono mempty
  mappend (RMono r1) (RMono r2) = RMono $ mappend r1 r2
  mappend (RMono r) (RPoly t)   = RPoly $ t `strengthen` r
  mappend (RPoly t) (RMono r)   = RPoly $ t `strengthen` r
  mappend (RPoly t1) (RPoly t2) = RPoly $ t1 `strengthenRefType_` t2

instance (Reftable r, Reftable (Predicate t)) => Reftable (UReft r t) where
  isTauto (U r p) = isTauto r && isTauto p 
  ppTy (U r p) d  = ppTy r (ppTy p d) 

instance (PVarable pv, Reftable r, Subable r) => RefTypable Class RTyCon RTyVar pv r where
  ppCls c ts  = parens $ pprClassPred c (toType <$> ts)

instance Outputable (PVar t) where
  ppr (PV s t xts) = ppr s <+> hsep (ppr <$> dargs xts)
    where dargs = map thd3 . takeWhile (\(_, x, y) -> x /= y) 
 
instance PVarable (PVar String) where
  ppr_def = ppr_pvar_def text

instance PVarable (PVar Type) where
  ppr_def = ppr_pvar_def ppr_pvar_type 

ppr_pvar_def pprv (PV s t xts) = ppr s <+> dcolon <+> intersperse arrow dargs 
  where dargs = [pprv t | (t,_,_) <- xts] ++ [pprv t, text boolConName]

ppr_pvar_type (TyVarTy α) = ppr_tyvar α
ppr_pvar_type t           = ppr t


-- isPVarDef (PV _ _ xts) = all (\(_, x, y) -> x == y) xts  


instance (RefTypable p c tv pv r) => Outputable (RType p c tv pv r) where
  ppr = ppRType TopPrec

instance Outputable (RType p c tv pv r) => Show (RType p c tv pv r) where
  show = showSDoc . ppr

instance Outputable RTyCon where
  ppr (RTyCon c ts) = ppr c 
  -- <+> text "\n<<" <+> hsep (map ppr ts) <+> text ">>\n"

instance Show RTyCon where
 show = showPpr

ppr_rtype :: (Subable r, RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc

ppr_rtype p t@(RAll _ _)       
  = ppr_forall p t
ppr_rtype p (RVar (RV a) r)         
  = ppTy r $ ppr a
ppr_rtype p (RFun x t t' _)  
  = pprArrowChain p $ ppr_dbind x t : ppr_fun_tail t'
ppr_rtype p ty@(RApp c [t] rs r)
  | isList c 
  = ppTy r $ brackets (ppr_rtype p t) <> ppReftPs rs
ppr_rtype p ty@(RApp c ts rs r)
  | isTuple c 
  = ppTy r $ parens (intersperse comma (ppr_rtype p <$> ts)) <> ppReftPs rs
ppr_rtype p (RApp c ts rs r)
  = ppTy r $ ppr c <+> ppReftPs rs <+> hsep (ppr_rtype p <$> ts)  
ppr_rtype _ ty@(RCls c ts)      
  = ppCls c ts
ppr_rtype _ (ROth s)
  = text "?" <> text s <> text "?"

ppReftPs rs 
  | all isTauto rs = empty -- text "" 
  | otherwise      = angleBrackets $ hsep $ punctuate comma $ ppr <$> rs

ppr_pred :: (Subable r, RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc
ppr_pred p (RAll pv@(RP _) t)
  = ppr pv <> ppr_pred p t
ppr_pred p t
  = dot <+> ppr_rtype p t

ppr_dbind :: (Subable r, RefTypable p c tv pv r) => Bind tv pv -> RType p c tv pv r -> SDoc
ppr_dbind b@(RB x) t 
  | isNonSymbol x 
  = ppr_rtype FunPrec t
  | otherwise
  = {-braces-} (ppr b) <> colon <> ppr_rtype FunPrec t

ppr_fun_tail :: (Subable r, RefTypable p c tv pv r) => RType p c tv pv r -> [SDoc]
ppr_fun_tail (RFun b t t' _)  
  = (ppr_dbind b t) : (ppr_fun_tail t')
ppr_fun_tail t
  = [ppr_rtype TopPrec t]

ppr_forall :: (Subable r, RefTypable p c tv pv r) => Prec -> RType p c tv pv r -> SDoc
ppr_forall p t
  = maybeParen p FunPrec $ sep [ppr_foralls αs, ppr_rtype TopPrec t']
  where
    (αs,  t')           = split [] t
    split αs (RAll α t) = split (α:αs) t
    split αs t	        = (reverse αs, t)
   
ppr_foralls [] = empty
ppr_foralls bs = text "forall" <+> dαs [ α | RV α <- bs] <+> dπs [ π | RP π <- bs] <> dot
  where dαs αs = sep $ ppr <$> αs 
        dπs [] = empty 
        dπs πs = angleBrackets $ intersperse comma $ ppr_def <$> πs

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

--instance Functor (UReft r) where 
--  fmap = second 

instance Bifunctor UReft where
  first f (U r p)  = U (f r) p
  second f (U r p) = U r (fmap f p)


instance Functor (RType a b c d) where
  fmap f = mapReft f


subsTyVars_meet   = subsTyVars True
subsTyVars_nomeet = subsTyVars False
subsTyVar_nomeet  = subsTyVar False
subsTyVar_meet    = subsTyVar True

subsTyVar meet        = subsFree meet S.empty
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats


subsFree ::  (SubsTy r, Reftable r, Subable r) => Bool -> S.Set RTyVar -> (RTyVar, RRType (PVar Type) r) -> RRType (PVar Type) r -> RRType (PVar Type) r 

subsFree m s z (RAll (RP p) t)         
  = RAll (RP p') t'
    where p' = subt (second toType z) p
          t' = subsFree m s z t
subsFree m s z (RAll (RV α) t)         
  = RAll (RV α) $ subsFree m (α `S.insert` s) z t
subsFree m s z (RFun x t t' r)       
  = RFun x (subsFree m s z t) (subsFree m s z t') (subt (second toType z)  r)
subsFree m s z@(α, t') t@(RApp c ts rs r)     
  = RApp c' (subsFree m s z <$> ts) (subsFreeRef m s z <$> rs) (subt z' r)  
    where c' = c {rTyConPs = subt z' <$> rTyConPs c}
          z' = (α, toType t')
    -- UNIFY: why instantiating INSIDE parameters?
subsFree m s z (RCls c ts)     
  = RCls c (subsFree m s z <$> ts)
subsFree meet s (α', t') t@(RVar (RV α) r) 
  | α == α' && α `S.notMember` s 
  = if meet then t' `strengthen`  r' else t' 
  | otherwise
  = {- traceShow  msg $ -} t
  where -- msg = ("subsFree MISS: α = " ++ showPpr α ++ " α' = " ++ showPpr α' ++ " s = " ++ showPpr s)
        r'  = subt (α', toType t') r

subsFree _ _ _ t@(ROth _)        
  = t
subsFree _ _ _ t      
  = errorstar $ "subsFree fails on: " ++ showPpr t

subsFreeRef ::  (SubsTy r, Reftable r, Monoid r, Subable r) => Bool -> S.Set RTyVar -> (RTyVar, RRType (PVar Type) r) -> Ref r (RRType (PVar Type) r) -> Ref r (RRType (PVar Type) r)
subsFreeRef m s z (RPoly t) 
  = RPoly $ subsFree m s z' t
  where (a, t') = z
        z' = (a, fmap (\_ -> top) t')
subsFreeRef m s z (RMono r) 
  = RMono $ subt (α, toType t) r
  where (α, t) = z

-------------------------------------------------------------------
------------------- Type Substitutions ----------------------------
-------------------------------------------------------------------

class SubsTy a where
  subp :: M.Map (PVar Type) (Predicate Type) -> a -> a
  subv :: (PVar Type -> PVar Type) -> a -> a
  subt :: (RTyVar, Type) -> a -> a
  
-- subts :: (SubsTy a) => [(RTyVar, Type)] -> a -> a 
subts = flip (foldr subt) 

lookupP s p@(PV _ _ s')
  = case M.lookup p s of 
      Nothing  -> Pr [p]
      Just q   -> subv (\pv -> pv { pargs = s'}) q

instance SubsTy Type where
  subp _ = id 
  subv _ = id 
  subt (α', t') t@(TyVarTy tv) 
    | α' == RTV tv = t'
    | otherwise    = t
  subt _ t = t -- UNIFY: Deep Subst

instance SubsTy Reft where
  subv _ = id 
  subp _ = id 
  subt _ = id

instance SubsTy (PVar Type) where
  subp _               = id
  subv f x             = f x
  subt su (PV n t xts) = PV n (subt su t) [(subt su t, x, y) | (t,x,y) <- xts] 

instance SubsTy (Predicate Type) where
  subv f (Pr pvs) = Pr (f <$> pvs)
  subp s (Pr pvs) = pdAnd (lookupP s <$> pvs) -- RJ: UNIFY: not correct!
  subt f (Pr pvs) = Pr (subt f <$> pvs)

instance SubsTy (UReft a Type) where
  subp f (U r p)  = U r (subp f p)
  subv f (U r p)  = U r (subv f p)
  subt f (U r p)  = U r (subt f p)

-- NOTE: This DOES NOT substitute at the binders
instance SubsTy PrType where    
  subp f t  = fmap (subp f) t
  subv f t  = fmap (subv f) t 
  subt      = subsTyVar_meet . second ofType 

substSym (x, y) = mapReft fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == x) then y else s
        fp    = subv (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

instance (SubsTy r)  => SubsTy (Ref r (RType a b c d r))  where
  subp m (RMono p) = RMono $ subp m p
  subp m (RPoly t) = RPoly $ fmap (subp m) t
  subv m (RMono p) = RMono $ subv m p
  subv m (RPoly t) = RPoly $ fmap (subv m) t
  subt m (RMono p) = RMono $ subt m p
  subt m (RPoly t) = RPoly $ fmap (subt m) t


---------------------------------------------------------------

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RApp _ _ _ x)   
  = Just x
stripRTypeBase (RVar _ x)   
  = Just x
stripRTypeBase (RFun _ _ _ x)   
  = Just x
stripRTypeBase _                
  = Nothing

-- ofType ::  Reftable r => Type -> RRType a r
ofType = ofType_ . expandTypeSynonyms 

ofType_ (TyVarTy α)     
  = rVar α top 
ofType_ (FunTy τ τ')    
  = rFun (RB dummySymbol) (ofType_ τ) (ofType_ τ') 
ofType_ (ForAllTy α τ)  
  = RAll (rTyVar α) $ ofType_ τ  
ofType_ τ
  | isPredTy τ
  = ofPredTree (classifyPredType τ)  
ofType_ τ@(TyConApp c τs)
  | TC.isSynTyCon c
  = ofType_ $ substTyWith αs τs τ
  | otherwise
  = rApp c (ofType_ <$> τs) [] top 
  where (αs, τ) = TC.synTyConDefn c
ofType_ τ               
  = error "ofType" -- ROth (show τ)  

ofPredTree (ClassPred c τs)
  = RCls c (ofType_ <$> τs)
ofPredTree _
  = error "ofPredTree"


-----------------------------------------------------------------
---------------------- Scrap this using SYB? --------------------
-----------------------------------------------------------------

mapReft f (RVar α r)       = RVar α (f r)
mapReft f (RAll a t)       = RAll a (mapReft f t)
mapReft f (RFun x t t' r)  = RFun x (mapReft f t) (mapReft f t') (f r)
mapReft f (RApp c ts rs r) = RApp c (mapReft f <$> ts) (mapRef f <$> rs) (f r)
mapReft f (RCls c ts)      = RCls c (mapReft f <$> ts) 
mapReft f (ROth a)         = ROth a 

mapRef f (RMono r) = RMono $ f r
mapRef f (RPoly t) = RPoly $ mapReft f t

isTautoTy (RVar α r)       = isTauto r
isTautoTy (RAll a t)       = isTautoTy t
isTautoTy (RFun x t t' r)  = isTautoTy t && isTautoTy t' && isTauto r
isTautoTy (RApp c ts rs r) = and $ (isTauto r):((isTautoTy <$> ts) ++ (isTautoRef <$> rs))
isTautoTy (RCls c ts)      = and (isTautoTy <$> ts) 
isTautoTy (ROth a)         = True

isTautoRef (RMono r) = isTauto r
isTautoRef (RPoly t) = isTauto t


--mapRVar :: (Bind tv pv -> r -> RType p c tv pv r)-> RType p c tv pv r -> RType p c tv pv r
--mapRVar f (RVar b r)       = f b r 
--mapRVar f (RFun b t1 t2 r) = RFun b (mapRVar f t1) (mapRVar f t2)
--mapRVar f (RAll b t)       = RAll b (mapRVar f t) 
--mapRVar f (RApp c ts rs r) = RApp c (mapRVar f <$> ts) rs r
--mapRVar f (RCls c ts)      = RCls c (mapRVar f <$> ts)
--mapRVar f (ROth s)         = ROth s

mapBind f (RVar b r)       = RVar (f b) r
mapBind f (RFun b t1 t2 r) = RFun (f b) (mapBind f t1) (mapBind f t2) r
mapBind f (RAll b t)       = RAll (f b) (mapBind f t) 
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RCls c ts)      = RCls c (mapBind f <$> ts)
mapBind f (ROth s)         = ROth s

mapBindRef _ (RMono r) = RMono r
mapBindRef f (RPoly t) = RPoly $ mapBind f t


mapBot f (RAll a t)       = RAll a (mapBot f t)
mapBot f (RFun x t t' r)  = RFun x (mapBot f t) (mapBot f t') r
mapBot f (RApp c ts rs r) = f $ RApp c (mapBot f <$> ts) (mapBotRef f <$> rs) r
mapBot f (RCls c ts)      = RCls c (mapBot f <$> ts)
mapBot f t'               = f t' 

mapBotRef _ (RMono r) = RMono $ r
mapBotRef f (RPoly t) = RPoly $ mapBot f t
-------------------------------------------------------------------
--------------------------- SYB Magic -----------------------------
-------------------------------------------------------------------

reftypeBindVars :: RefType -> S.Set Symbol
reftypeBindVars = everything S.union (S.empty `mkQ` grabBind)
  where grabBind ((RB x) :: RBind) = S.singleton x 

readSymbols :: (Data a) => a -> S.Set Symbol
readSymbols = everything S.union (S.empty `mkQ` grabRead)
  where grabRead (EVar x) = S.singleton x
        grabRead _        = S.empty

---------------------------------------------------------------------
---------- Cleaning Reftypes Up Before Rendering --------------------
---------------------------------------------------------------------

tidyRefType :: RefType -> RefType
tidyRefType = tidyDSymbols
            . tidySymbols 
            . tidyFunBinds
            . tidyLocalRefas 
            . tidyTyVars 

tidyFunBinds :: RefType -> RefType
tidyFunBinds t = everywhere (mkT $ dropBind xs) t 
  where xs = readSymbols t
        dropBind xs ((RB x) :: RBind) 
          | x `S.member` xs = RB x
          | otherwise       = RB nonSymbol
        dropBind _ z = z

tidyTyVars :: RefType -> RefType
tidyTyVars = tidy pool getS putS 
  where getS (α :: TyVar)   = Just (symbolString $ mkSymbol α)
        putS (α :: TyVar) x = stringTyVar x
        pool          = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]

tidyLocalRefas :: RefType -> RefType
tidyLocalRefas = everywhere (mkT dropLocals) 
  where dropLocals = filter (not . Fold.any isTmp . readSymbols) . flattenRefas
        isTmp x    = let str = symbolString x in 
                     (anfPrefix `isPrefixOf` str) || (tempPrefix `isPrefixOf` str) 

tidySymbols :: RefType -> RefType
tidySymbols = everywhere (mkT dropSuffix) 
  where dropSuffix = stringSymbol . takeWhile (/= symSep) . symbolString
        dropQualif = stringSymbol . dropModuleNames . symbolString 

tidyDSymbols :: RefType -> RefType
tidyDSymbols = tidy pool getS putS 
  where getS   sy  = let str = symbolString sy in 
                     if "ds_" `isPrefixOf` str then Just str else Nothing
        putS _ str = stringSymbol str 
        pool       = ["X" ++ show i | i <- [1..]]

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------

symSep = '#'

mkSymbol ::  Var -> Symbol
mkSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSep] ++ us
  where us  = showPpr $ getUnique v 
        vs  = pprShort v

dataConSymbol = mkSymbol . dataConWorkId

primOrderingSort = typeSort $ dataConRepType eqDataCon
ordCon s = EDat (S s) primOrderingSort

-- TODO: turn this into a map lookup?
-- dataConReft   ::  DataCon -> Type -> Reft 
dataConReft c τ
  | c == trueDataCon
  = Reft (vv, [RConc $ (PBexp (EVar vv))]) 
  | c == falseDataCon
  = Reft (vv, [RConc $ PNot (PBexp (EVar vv))]) 
  | c == eqDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "EQ"))]) 
  | c == gtDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "GT"))]) 
  | c == ltDataCon
  = Reft (vv, [RConc (PAtom Eq (EVar vv) (ordCon "LT"))]) 
  | otherwise
  = Reft (vv, [RConc PTrue]) 

dataConMsReft ty ys  = subst su r 
  where (_, xts, t)  = bkArrow ty 
        r            = fromMaybe trueReft $ stripRTypeBase t
        su           = mkSubst [(x, EVar y) | ((x,_), y) <- zip xts ys] 

pprShort    =  dropModuleNames . showPpr


---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------

toType ::  RRType a b -> Type

toType (RFun _ t t' _)   
  = FunTy (toType t) (toType t')
toType (RAll (RV (RTV α)) t)      
  = ForAllTy α (toType t)
toType (RVar (RV (RTV α)) _)        
  = TyVarTy α
toType (RApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
toType (RCls c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
  -- = PredTy (ClassP c (toType <$> ts))
toType (ROth t)      
  = errorstar $ "toType fails: " ++ t

---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

literalRefType l 
  = makeRTypeBase (literalType l) (literalReft l) 

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α) x       
  = RVar (rTyVar α) x 
makeRTypeBase τ@(TyConApp c _) x 
  = rApp c [] [] x

literalReft l  = exprReft e 
  where (_, e) = literalConst l 

literalConst l                 = (sort, mkLit l)
  where sort                   = typeSort $ literalType l 
        sym                    = stringSymbol $ "$$" ++ showPpr l
        mkLit (MachInt    n)   = mkI n
        mkLit (MachInt64  n)   = mkI n
        mkLit (MachWord   n)   = mkI n
        mkLit (MachWord64 n)   = mkI n
        mkLit (LitInteger n _) = mkI n
        mkLit _                = ELit sym sort
        mkI                    = ECon . I

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

newtype REnv = REnv  (M.Map Symbol RefType)
               deriving (Data, Typeable)

fromListREnv              = REnv . M.fromList
deleteREnv x (REnv env)   = REnv (M.delete x env)
insertREnv x y (REnv env) = REnv (M.insert x y env)
lookupREnv x (REnv env)   = M.lookup x env
emptyREnv                 = REnv M.empty
memberREnv x (REnv env)   = M.member x env
domREnv (REnv env)        = M.keys env


instance Outputable REnv where
  ppr (REnv m)         = vcat $ map pprxt $ M.toAscList m
    where pprxt (x, t) = ppr x <> dcolon <> ppr t  

refTypePredSortedReft (r, τ) = RR so r
  where so = typeSort τ

refTypeSortedReft   ::  RefType -> SortedReft
refTypeSortedReft t = RR so r
  where so = {- traceShow ("rTypeSort: t = " ++ showPpr t) $ -} rTypeSort t
        r  = fromMaybe trueReft $ stripRTypeBase t 

-- RJ: Commenting this out. Why is FFunc not working?
-- funcToObj (RR (FFunc _ _) r) = RR FObj r
funcToObj so                 = so

-- typeSortedReft ::  Type -> Refa -> SortedReft
typeSortedReft t r = RR (typeSort t) (Reft (vv, [r]))


-- rTypeSort ::  RType t -> Sort
rTypeSort = typeSort . toType

-------------------------------------------------------------------
-------------------------- Substitution ---------------------------
-------------------------------------------------------------------

instance Subable RefType  where
  subst = fmap . subst 

instance Subable (UReft Reft String) where
  subst s (U r p) = U (subst s r) p

instance Subable (UReft Reft Type) where
  subst s (U r p) = U (subst s r) p

instance Subable (Predicate Type) where
  subst _ = id 

instance Subable r => Subable (RType p c tv pv r) where
  subst  = fmap . subst

