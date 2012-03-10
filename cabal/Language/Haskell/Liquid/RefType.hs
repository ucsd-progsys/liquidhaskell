{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}


{- Refinement Types Mirroring the GHC Type definition -}

module Language.Haskell.Liquid.RefType (
    RTyCon (..), RAlgRhs (..), RDataCon (..), RType (..)
  , RefType (..), RefTyCon (..), RefAlgRhs (..), RefDataCon (..)  
  , RBind (..), RTyVar
  , ofType
  , rTyVar, rTyVarSymbol --, rTyConApp
  , typeId -- , typeUniqueString
  , strengthen, strengthenRefType
  , unfoldRType, mkArrow
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, refTypeSortedReft, rTypeSort
  , canonRefType, tidyRefType
  , mkSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalConst
  , REnv, deleteREnv, insertREnv, lookupREnv, emptyREnv, memberREnv, fromListREnv
  , replaceDcArgs, rCon
  ) where

import Text.Printf
import Control.Exception.Base
import Control.Exception (assert)
import GHC
import Outputable
import qualified TyCon as TC
import DataCon
import TypeRep 

import Var
import VarEnv
import PrelNames
import Name             (getSrcSpan, getOccString, mkInternalName)
import Unique           (getUnique)
import Literal
import Type             (isPredTy, mkTyConTy, liftedTypeKind, substTyWith, classifyPredType, PredTree(..), predTreePredType)
import TysPrim          (intPrimTyCon)
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon)


import Data.Maybe               (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S 
import Control.Applicative  hiding (empty)   
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq
import qualified Data.Foldable as Fold

import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc2 (stringTyVar)
import Data.List (isPrefixOf, isSuffixOf, find, foldl')

--------------------------------------------------------------------
---------------------- Refinement Types ----------------------------
--------------------------------------------------------------------

newtype TyId 
  = TI String deriving (Eq, Ord, Show, Data, Typeable)

typeId :: TC.TyCon -> TyId
typeId = TI . showPpr

data RTyCon a  
  = RAlgTyCon { 
      rTyCon        :: !TC.TyCon
    , rAlgTcRhs     :: !(RAlgRhs a) 
    }
  | RPrimTyCon {    
      rTyCon        :: !TC.TyCon
    }
  deriving (Data, Typeable)

data RAlgRhs a 
  = RDataTyCon { 
      rAlgRhs       :: () --TC.AlgTyConRhs DO NOT DELETE!, 
    , rdata_cons    :: ![RDataCon a] 
    } 
  deriving (Data, Typeable)

data RDataCon a  
  = MkRData { 
      rdcDataCon    :: !DataCon
    , rdcOrigArgTys :: ![(RBind, RType a)] 
    } 
  deriving (Data, Typeable)

newtype RBind = RB Symbol
  deriving (Data, Typeable)

newtype RTyVar = RT (TyVar, Symbol)
  deriving (Eq, Ord, Data, Typeable)

data RType a 
  = RVar   !RTyVar !a
  | RFun   !RBind  !(RType a) !(RType a)
  | RAll   !RTyVar !(RType a)
  | RCon   !TyId   !(RTyCon a) ![RType a] !a
  | RClass !Class  ![RType a]
  | RMuVar !TyId   ![RType a] 
  | ROther !Type 
  deriving (Data, Typeable)

type RefTyCon   = RTyCon Reft 
type RefAlgRhs  = RAlgRhs Reft  
type RefDataCon = RDataCon Reft 
type RefType    = RType Reft    

instance Show RefTyCon where
  show = showPpr

instance Show RefType where
  show = showPpr

rTyVar α = RT (α, mkSymbol α)
rTyVarSymbol (RT (α, _)) = S $ typeUniqueString $ TyVarTy α

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

strengthenRefType :: RefType -> RefType -> RefType
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = error $ "strengthen on differently shaped reftypes! " 
          ++ "t1 = " ++ showPpr t1 
          ++ "t2 = " ++ showPpr t2
  where eqt t1 t2 = showPpr (toType t1) == showPpr (toType t2)
  
strengthenRefType_ (RAll a t1) (RAll _ t2)
  = RAll a $ strengthenRefType_ t1 t2

strengthenRefType_ (RFun (RB x1) t1 t1') (RFun (RB x2) t2 t2') 
  = RFun (RB x1) t t'
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RCon tid tc t1s r1) (RCon _ _ t2s r2)
  = rCon tid tc ts (r1 `meet` r2)
    where ts = zipWith strengthenRefType_ t1s t2s

strengthenRefType_ t1 _ 
  = t1

strengthen  :: RefType -> Reft -> RefType
strengthen (RCon i c ts r) r' = rCon i c ts (r `meet` r') 
strengthen (RVar a r) r'      = RVar a      (r `meet` r') 
strengthen t _                = t 


replaceReft  :: RefType -> Reft -> RefType
replaceReft (RCon i c ts _) r' = rCon i c ts r' 
replaceReft (RVar a _) r'      = RVar a      r' 
replaceReft t _                = t 


-- inside the rc, the αs are refined by "zombie" kvars with
-- no constraints (ie false). So "meeting" with them is
-- unsound. (see tests/neg/mapreduce-tiny.hs)
unfoldRType :: DataCon -> RefType -> [(Symbol, RefType)]
unfoldRType dc t@(RCon i rc ts _) 
--  = [(f, {-sub-} ft {-`strengthen` (F.symbolReft f))-} | (RB f, ft) <- rdcOrigArgTys rdc] 
  = [(f, sub ft) | (RB f, ft) <- rdcOrigArgTys rdc] 
  where rdc = getRDataCon dc rc 
        MkRData _ rxts = rdc
        (rxs, rts) = unzip rxts
        sub = subsTyId t i rc . subsTyVars_nomeet αts
        αts = safeZip "unfoldRType"  αs ts
        αs  = rTyVar `fmap` (dataConUnivTyVars $ rdcDataCon rdc)
--rTyConApp' :: RefTyCon -> [RefType] -> RefTyCon
--rTyConApp' rc _ = rc
--rTyConApp' rc@(RPrimTyCon _) _ 
--  = rc
--rTyConApp' rc@(RAlgTyCon c _) ts 
--  = subsTyVarsTyCon False αts rc
--    where αts = safeZip "rTyConApp"  αs ts
--          αs  = rTyVar `fmap` (tyConTyVars c) 
--
--rTyConApp rc ts 
--  = traceShow ("rTyConApp rc = " ++ showPpr rc) $ rTyConApp' rc ts 



getRDataCon dc (RAlgTyCon _ (RDataTyCon _ rdcs)) 
  = mfromJust "findRDataCon" $ find ((dc ==) . rdcDataCon) rdcs

subsTyId t i rc = mapBot plug 
  where plug (RMuVar j ts) | i == j = rCon i rc ts trueReft
        plug t                      = t
         
mkArrow ::  [TyVar] -> [(Symbol, RType a)] -> RType a -> RType a
mkArrow as xts t = mkUnivs as $ mkArrs xts t

mkUnivs αs t  = tr_foldr' RAll t $ rTyVar `fmap` αs
mkArrs xts t = tr_foldr' (\(x,t) -> RFun (RB x) t) t xts

bkArrow :: RType a -> ([TyVar], [(Symbol, RType a)],  RType a)
bkArrow ty = (αs, xts, out)
  where (αs, t)    = bkUniv [] ty
        (xts, out) = bkArrs [] t
        
bkUniv as (RAll a t) = bkUniv (a:as) t
bkUniv as t          = ((reverse $ fmap (\(RT (α,_)) -> α) as), t)

bkArrs xts (RFun (RB x) t t') = bkArrs ((x,t):xts) t'
bkArrs xts t                  = (reverse xts, t)

----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData TyId where 
  rnf (TI x)  = rnf x

instance NFData REnv where
  rnf (REnv m) = () -- rnf m

instance NFData RBind where
  rnf (RB x) = rnf x

instance NFData RTyVar where
  rnf (RT (_,x)) = rnf x

instance (NFData a) => NFData (RTyCon a) where
  rnf (RAlgTyCon x1 x2) = x1 `seq` rnf x2 
  rnf (RPrimTyCon x)    = x `seq` () 


instance (NFData a) => NFData (RAlgRhs a) where
  rnf (RDataTyCon x1 x2) = rnf x1 `seq` rnf x2 

instance (NFData a) => NFData (RDataCon a) where
  rnf (MkRData x1 x2)    = x1 `seq` rnf x2
   
instance (NFData a) => NFData (RType a) where
  rnf (RVar α r)      = rnf α `seq` rnf r 
  rnf (RAll α t)      = rnf α `seq` rnf t
  rnf (RFun x t t')   = rnf x `seq` rnf t `seq` rnf t'
  rnf (RCon i c ts r) = rnf i `seq` rnf c `seq` rnf ts `seq` rnf r
  rnf (RClass c ts)   = c `seq` rnf ts
  rnf (RMuVar i ts)   = rnf i `seq` rnf ts
  rnf (ROther a)      = ()


----------------------------------------------------------------
---------------------- Refinement Types ------------------------
----------------------------------------------------------------

instance Outputable RBind where
  ppr (RB x) = ppr x

instance Show RBind where
  show = showPpr 
 
instance Show RTyVar where
  show = showPpr

instance Outputable RTyVar where
  ppr (RT (_, x)) = ppr x

instance Outputable RefType where
  ppr = ppr_reftype TopPrec 


instance Outputable RefTyCon where
  ppr = ppr_rcon

instance Outputable RefDataCon where
  ppr = ppr_rdatacon

ppr_reftype p (RVar a r)         
  = ppReft r $ ppr a
ppr_reftype p (RFun x t t')      
  = pprArrowChain p $ ppr_dbind x t : ppr_fun_tail t'
ppr_reftype p t@(RAll _ _)       
  = ppr_forall_reftype p t
ppr_reftype p (RCon _ c ts r)    
  = ppReft r $ pprTcApp p ppr_reftype (rTyCon c) ts 
    <> ppr_rcon c                -- ONLY FOR DEBUGGING, DO NOT DELETE.
    -- <> ppr_rcon (rTyConApp c ts) -- ONLY FOR DEBUGGING, DO NOT DELETE.

ppr_reftype _ (RClass c ts)      
  = parens $ pprClassPred c (toType <$> ts)
ppr_reftype _ (RMuVar (TI s) ts) 
  = text s <> text "@mu" <> ppr ts 
ppr_reftype _ (ROther t)         
  = text "?" <> ppr t <> text "?"
 
ppr_rcon (RAlgTyCon _ (RDataTyCon _ rdcs)) 
  = text "<<<" <> sep ((text "||") `punctuate` (ppr_rdatacon `fmap` rdcs)) <> text ">>>"
  
ppr_rcon (RPrimTyCon _)    
  = empty

ppr_rdatacon (MkRData d bs) 
  = ppr d <> text " of " <> sep ((text "&&") `punctuate` (ppr `fmap` bs)) 

ppr_dbind (RB x) t 
  | x == nonSymbol
  = ppr_reftype FunPrec t
  | otherwise
  = ppr x <> text ":" <> ppr_reftype FunPrec t

ppr_fun_tail (RFun x t t')  
  = (ppr_dbind x t) : (ppr_fun_tail t')
ppr_fun_tail t
  = [ppr t]

ppr_forall_reftype :: Prec -> RefType -> SDoc
ppr_forall_reftype p t
  = maybeParen p FunPrec $ sep [ppr_foralls αs, ppr_reftype TopPrec t']
  where
    (αs,  t')           = split [] t
    split αs (RAll α t) = split (α:αs) t
    split αs t	        = (reverse αs, t)

ppr_foralls :: [RTyVar] -> SDoc
ppr_foralls []  = empty
ppr_foralls tvs = (text "forall") <+> sep (map ppr tvs) <> dot

ppReft (Reft (v, ras)) d 
  | all isTautoRa ras
  = d
  | otherwise
  =  braces (ppr v <> text ":" <> d <> text " | " <> ppRas ras)

isTautoRa (RConc p) = isTauto p
isTautoRa _         = False

ppRas = cat . punctuate (text ",") . map toFix . flattenRefas

       
---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

instance Functor RTyCon where
  fmap f (RAlgTyCon x z)  = RAlgTyCon x (f <$> z)
  fmap f (RPrimTyCon c)   = RPrimTyCon c 

instance Functor RAlgRhs where
  fmap f (RDataTyCon x y) = RDataTyCon x (map (f <$>) y)

instance Functor RDataCon where
  fmap f (MkRData x y) = MkRData x (map (mapSnd (f <$>)) y)
   
instance Functor RType where
  fmap f (RVar α r)      = RVar α (f r)
  fmap f (RAll a t)      = RAll a (fmap f t)
  fmap f (RFun x t t')   = RFun x (fmap f t) (fmap f t')
  fmap f (RCon i c ts r) = RCon i (fmap f c) (fmap (fmap f) ts) (f r)
  fmap f (RClass c ts)   = RClass c (fmap (fmap f) ts)
  fmap f (RMuVar i ts)   = RMuVar i (fmap (fmap f) ts)
  fmap f (ROther a)      = ROther a 

subsTyVars_meet   = subsTyVars True
subsTyVars_nomeet = subsTyVars False
subsTyVar_meet    = subsTyVar True
subsTyVar_nomeet  = subsTyVar False

subsTyVars ::  Bool -> [(RTyVar, RefType)] -> RefType -> RefType 
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats

subsTyVarsTyCon ::  Bool -> [(RTyVar, RefType)] -> RefTyCon -> RefTyCon
subsTyVarsTyCon meet ats c = foldl' (flip (subsFreeRTyCon meet S.empty)) c ats

subsTyVar ::  Bool -> (RTyVar, RefType) -> RefType -> RefType 
subsTyVar meet = subsFree meet S.empty

subsFree ::  Bool -> S.Set RTyVar -> (RTyVar, RefType) -> RefType -> RefType
subsFree m s z (RAll α' t)         
  = RAll α' $ subsFree m (α' `S.insert` s) z t
subsFree m s z (RFun x t t')       
  = RFun x (subsFree m s z t) (subsFree m s z t') 
subsFree m s z (RCon i c ts r)     
  = rCon i (subsFreeRTyCon m s z c) (subsFree m s z <$> ts) r 
subsFree m s z (RClass c ts)     
  = RClass c (subsFree m s z <$> ts)
subsFree meet s (α', t') t@(RVar α r) 
  | α == α' && α `S.notMember` s 
  = if meet then t' `strengthen` r else t' 
  | otherwise
  = t
subsFree m s z (RMuVar i ts)
  = RMuVar i (subsFree m s z <$> ts)
subsFree _ _ _ t@(ROther _)        
  = t

subsFreeRTyCon m s z (RAlgTyCon p r) 
  = RAlgTyCon p (subsFreeRAlgRhs m s z r)
subsFreeRTyCon m s z x@(RPrimTyCon _)         
  = x 
subsFreeRAlgRhs m s z (RDataTyCon p dcs) 
  = RDataTyCon p (subsFreeRDataCon m s z <$> dcs)
subsFreeRDataCon m s z (MkRData p qs) 
  = MkRData p (map (mapSnd $ subsFree m s z) qs)

---------------------------------------------------------------

tyConRTyCon c  
  | isPrimTyCon c = RPrimTyCon c
  | otherwise     = error $ "tyConRTyCon: " ++ showPpr c


stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RCon _ _ _ x)   
  = Just x
stripRTypeBase (RVar _ x)   
  = Just x
stripRTypeBase _                
  = Nothing


ofType :: Type -> RefType
ofType τ = --traceShow ("ofType τ = " ++ showPpr τ) $ 
           ofType_ S.empty τ

ofType_ :: S.Set TyId -> Type -> RefType 
ofType_ s (FunTy τ τ')    
  = RFun (RB dummySymbol) (ofType_ s τ) (ofType_ s τ')
ofType_ s (ForAllTy α τ)  
  = RAll (rTyVar α) $ ofType_ s τ  
ofType_ s (TyVarTy α)     
  = RVar (rTyVar α) trueReft 
ofType_ s τ
  | isPredTy τ
  = ofPredTree s (classifyPredType τ)  
ofType_ s τ@(TyConApp c _)
  | TC.isPrimTyCon c   
  = ofPrimTyConApp s τ
  | TC.isAlgTyCon c 
  = ofAlgTyConApp s τ
  | TC.isSynTyCon c
  = ofSynTyConApp s τ
  | otherwise
  = error $ "ofType: cannot handle tycon app: " ++ showPpr τ
ofType_ _ τ               
  = ROther τ  

ofPredTree s (ClassPred c τs)
  = RClass c (ofType_ s <$> τs)
 

ofPrimTyConApp s τ@(TyConApp c τs) 
  = rCon i rc ts trueReft 
  where i  = typeId c
        rc = RPrimTyCon c
        ts = ofType_ s <$> τs

ofSynTyConApp s (TyConApp c τs) 
  = ofType_ s $ substTyWith αs τs τ
  where (αs, τ) = TC.synTyConDefn c

ofAlgTyConApp s τ@(TyConApp c τs)
  | i `S.member` s
  = RMuVar i ts
  | otherwise
  = RCon i rc ts trueReft --(tyConReft c) 
  where i    = typeId c
        rc   = RAlgTyCon c $ ofAlgRhs (i `S.insert` s) (TC.algTyConRhs c)
        ts   = ofType_ s <$> τs

ofAlgRhs  :: S.Set TyId -> TC.AlgTyConRhs -> RefAlgRhs
ofAlgRhs s r 
  = RDataTyCon () (ofDataCon s <$> TC.visibleDataCons r)

ofDataCon :: S.Set TyId -> DataCon -> RefDataCon
ofDataCon s d
  = MkRData d $ zip flds ts
    where flds = (RB . intSymbol "fld") <$> [0..((length ts) - 1)]
          ts   = ofType_ s <$> dataConOrigArgTys d

-----------------------------------------------------------------
---------------------- Scrap this using SYB? --------------------
-----------------------------------------------------------------

mapTop ::  (RefType -> RefType) -> RefType -> RefType
mapTop f t = 
  case f t of
    (RAll a t')     -> RAll a (mapTop f t')
    (RFun x t' t'') -> RFun x (mapTop f t') (mapTop f t'')
    (RCon i c ts r) -> rCon i (mapTopRTyCon f c) (mapTop f <$> ts) r -- fix
    (RClass c ts)   -> RClass c (mapTop f <$> ts)
    t'              -> t' 

mapTopRTyCon f (RAlgTyCon p r)  
  = RAlgTyCon p (mapTopRAlgRhs f r)
mapTopRTyCon f x@(RPrimTyCon _) 
  = x 
mapTopRAlgRhs f (RDataTyCon p dcs)
  = RDataTyCon p (mapTopRDataCon f <$> dcs)
mapTopRDataCon f (MkRData p qs) 
  = MkRData p ((mapSnd $ mapTop f) <$> qs)

--mapBot ::  (RType a -> RType a) -> RType a -> RType a
mapBot ::  (RefType -> RefType) -> RefType -> RefType
mapBot f (RAll a t)      = RAll a (mapBot f t)
mapBot f (RFun x t t')   = RFun x (mapBot f t) (mapBot f t')
mapBot f (RCon i c ts r) = rCon i (mapBotRTyCon f c) (mapBot f <$> ts) r --fix
mapBot f (RClass c ts)   = RClass c (mapBot f <$> ts)
mapBot f t'              = f t' 

mapBotRTyCon f (RAlgTyCon p r)  
  = RAlgTyCon p (mapBotRAlgRhs f r)
mapBotRTyCon f x@(RPrimTyCon _) 
  = x 
mapBotRAlgRhs f (RDataTyCon p dcs)
  = RDataTyCon p (mapBotRDataCon f <$> dcs)
mapBotRDataCon f (MkRData p qs)  
  = MkRData p ((mapSnd $ mapBot f) <$> qs)

canonRefType :: RefType -> RefType
canonRefType = mapTop zz
  where zz t@(RCon i c ts r)  = rCon i c ts $ canonReft r
        zz t                  = t

-------------------------------------------------------------------
--------------------------- SYB Magic -----------------------------
-------------------------------------------------------------------

reftypeBindVars :: RefType -> S.Set Symbol
reftypeBindVars = everything S.union (S.empty `mkQ` grabBind)
  where grabBind (RB x) = S.singleton x 

readSymbols :: (Data a) => a -> S.Set Symbol
readSymbols = everything S.union (S.empty `mkQ` grabRead)
  where grabRead (EVar x) = S.singleton x
        grabRead _        = S.empty

-------------------------------------------------------------
---------- Cleaning Reftypes Up Before Rendering ------------
-------------------------------------------------------------

tidyRefType :: RefType -> RefType
tidyRefType = tidyDSymbols
            . tidySymbols 
            . tidyFunBinds
            . tidyLocalRefas 
            . tidyTyVars 

tidyFunBinds :: RefType -> RefType
tidyFunBinds t = everywhere (mkT $ dropBind xs) t 
  where xs = readSymbols t
        dropBind xs (RB x) 
          | x `S.member` xs = RB x
          | otherwise       = RB nonSymbol

tidyTyVars :: RefType -> RefType
tidyTyVars = tidy pool getS putS 
  where getS (RT (_, S x)) = Just x
        putS (RT (α, _)) x = RT ({- α -} stringTyVar x, S x) 
        pool               = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]

--tidyTyVars' r = traceShow ("tidyTyVars: " ++ show r) $ tidyTyVars r 

tidyLocalRefas :: RefType -> RefType
tidyLocalRefas = everywhere (mkT dropLocals) 
  where dropLocals  = filter (not . Fold.any isTmp . readSymbols) . flattenRefas
        isTmp (S x) = (anfPrefix `isPrefixOf` x) || (tempPrefix `isPrefixOf` x) 

tidySymbols :: RefType -> RefType
tidySymbols = everywhere (mkT dropSuffix) 
  where dropSuffix (S x) = S (takeWhile (/= symSep) x)
        dropQualif (S x) = S (dropModuleNames x)

tidyDSymbols :: RefType -> RefType
tidyDSymbols = tidy pool getS putS 
  where getS (S x)   = if "ds_" `isPrefixOf` x then Just x else Nothing
        putS (S _) x = S x
        pool         = ["X" ++ show i | i <- [1..]]

----------------------------------------------------------------
------------------- Converting to Fixpoint ---------------------
----------------------------------------------------------------

symSep = '#'

mkSymbol ::  Var -> Symbol
mkSymbol v 
  | us `isSuffixOf` vs = S $ vs  
  | otherwise          = S $ vs ++ [symSep] ++ us
  where us  = showPpr $ getUnique v 
        vs  = pprShort v

dataConSymbol = mkSymbol . dataConWorkId

dataConReft   ::  DataCon -> Type -> Reft 
dataConReft c τ
  | c == trueDataCon
  = Reft (vv, [RConc $ (PBexp (EVar vv))]) 
  | c == falseDataCon
  = Reft (vv, [RConc $ PNot (PBexp (EVar vv))]) 
  | otherwise
  = Reft (vv, [RConc PTrue]) 

dataConMsReft ty ys  = subst su r 
  where (_, xts, t)  = bkArrow ty 
        r            = fromMaybe trueReft $ stripRTypeBase t
        su           = mkSubst [(x, EVar y) | ((x,_), y) <- zip xts ys] 

pprShort    =  dropModuleNames . showPpr

dropModuleNames = last . words . (dotWhite <$>) 
  where dotWhite '.' = ' '
        dotWhite c   = c

---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------

toType :: RType t -> Type
toType (RFun _ t t')   
  = FunTy (toType t) (toType t')
toType (RAll (RT (α,_))  t)      
  = ForAllTy α (toType t)
toType (RVar (RT (α,_)) _)        
  = TyVarTy α
toType (RCon _ c ts _)   
  = TyConApp (rTyCon c) (toType <$> ts)
toType (RClass c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
  -- = PredTy (ClassP c (toType <$> ts))
toType (ROther t)      
  = t 

typeSort :: Type -> Sort 
typeSort (TyConApp c []) 
  | k == intTyConKey     = FInt
  | k == intPrimTyConKey = FInt
  | k == integerTyConKey = FInt 
  | k == boolTyConKey    = FBool
  where k = TC.tyConUnique c
typeSort (ForAllTy _ τ) 
  = typeSort τ  -- JHALA: Yikes! Fix!!!
typeSort (FunTy τ1 τ2) 
  = typeSortFun τ1 τ2
typeSort τ
  = FPtr $ FLoc $ typeUniqueString τ
typeSortFun τ1 τ2
  = FFunc n $ genArgSorts sos
  where sos  = typeSort <$> τs
        τs   = τ1  : grabArgs [] τ2
        n    = (length sos) - 1
     
typeUniqueString :: Type -> String
typeUniqueString = ("sort#" ++) . showSDocDump . ppr

grabArgs τs (FunTy τ1 τ2 ) = grabArgs (τ1:τs) τ2
grabArgs τs τ              = reverse (τ:τs)

genArgSorts :: [Sort] -> [Sort]
genArgSorts xs = zipWith genIdx xs $ memoIndex genSort xs
  where genSort FInt        = Nothing
        genSort FBool       = Nothing 
        genSort so          = Just so
        genIdx  _ (Just i)  = FPtr (FLvar i) --FVar i
        genIdx  so  _       = so


---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

literalRefType l 
  = makeRTypeBase (literalType l) (literalReft l) 

--makeRTypeBase :: Type -> a -> RType a 
makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α) x       
  = RVar (rTyVar α) x 
makeRTypeBase τ@(TyConApp c []) x 
  = rCon (typeId c) (tyConRTyCon c) [] x
--fix
literalReft l  = exprReft e 
  where (_, e) = literalConst l 

literalConst l               = (sort, mkLit l)
  where sort                 = typeSort $ literalType l 
        sym                  = S $ "$$" ++ showPpr l
        mkLit (MachInt    n) = mkI n
        mkLit (MachInt64  n) = mkI n
        mkLit (MachWord   n) = mkI n
        mkLit (MachWord64 n) = mkI n
        mkLit (lit)          = ELit sym sort
        mkI                  = ECon . I

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

instance Outputable REnv where
  ppr (REnv m)         = vcat $ map pprxt $ M.toAscList m
    where pprxt (x, t) = ppr x <> text " :: " <> ppr t  


refTypeSortedReft   ::  RType Reft -> SortedReft
refTypeSortedReft t = RR so r
  where so = {- traceShow ("rTypeSort: t = " ++ showPpr t) $ -} rTypeSort t
        r  = fromMaybe trueReft $ stripRTypeBase t 

rTypeSort ::  RType t -> Sort
rTypeSort = typeSort . toType



-------------------------------------------------------------------
-------------------------- Substitution ---------------------------
-------------------------------------------------------------------

instance Subable RefType  where
  subst = fmap . subst 


rCon i c ts r = {-traceShow "RdataCon" $-} RCon i c' ts r
  where c' = replaceAlgTyConTys c ts

replaceAlgTyConTys (RAlgTyCon d (RDataTyCon i dcs)) ts
  = (RAlgTyCon d (RDataTyCon i dcs'))
     where dcs' = [MkRData dc (f dc lts) | (MkRData dc lts) <- dcs]
           f dc = map  (replaceTys (zip (dataConUnivTyVars dc) ts))

replaceAlgTyConTys alg _ = alg

{-  
replaceTys [] (l, t) = (l, t)
replaceTys ((t1, t2):tys) lt@(l, (RVar (RT (v, s)) a)) --refine 
 | t1 == v = (l, t2 `strengthen` a) 
 | otherwise = replaceTys tys lt 
-}

replaceTys t12s lt@(l, (RVar (RT (v, s)) a)) 
  = case (find ((==v) . fst) t12s) of 
      Just (_, t) -> (l, t `replaceReft` a) 
      Nothing     -> lt
 
replaceTys _     lt = lt


replaceDcArgs ls dc (RCon a (RAlgTyCon d (RDataTyCon e x)) b c) 
  = rCon a (RAlgTyCon d (RDataTyCon e x')) b c
 where x' = map (rplArgs dc ls) x

rplArgs don ls mkr@(MkRData {rdcDataCon = dc, rdcOrigArgTys = ts}) 
 | dc == don = MkRData {rdcDataCon = dc, rdcOrigArgTys = ls'}
 | otherwise = mkr
    where ls'  = {-traceShow ("mplampla" ++ showPpr t) $-} zip (map fst ts) (map snd ls)
          t = MkRData {rdcDataCon = dc, rdcOrigArgTys = ls'} 
