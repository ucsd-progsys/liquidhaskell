{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}


{- Refinement Types Mirroring the GHC Type definition -}

module Language.Haskell.Liquid.RefType (
    RType (..), RTyCon(..), RefTypable (..)
  , ppr_rtype
  , RefType (..)  
  , Bind (..), RBind
  , ofType, toType
  , rTyVar, rTyVarSymbol
  , strengthen, strengthenRefType
  , mkArrow, normalizePds, rsplitVsPs, rsplitArgsRes
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, refTypePredSortedReft_,refTypeSortedReft, typeSortedReft, refTypePredSortedReft, rTypeSort
  , canonRefType, tidyRefType
  , mkSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalConst
  , REnv, deleteREnv, domREnv, insertREnv, lookupREnv, emptyREnv, memberREnv, fromListREnv
  , addTyConInfo
  , primOrderingSort
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
import TysWiredIn       (listTyCon, intTy, intTyCon, boolTyCon, intDataCon, trueDataCon, falseDataCon, eqDataCon, ltDataCon, gtDataCon)


import Data.Maybe               (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S 
import Control.Applicative  hiding (empty)   
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq
import qualified Data.Foldable as Fold

import Language.Haskell.Liquid.PredType hiding (subsTyVars)
import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc2 (stringTyVar)
import Data.List (isPrefixOf, isSuffixOf, find, foldl')

--------------------------------------------------------------------
------------------ Generic Type Representation ---------------------
--------------------------------------------------------------------

-- data RBind = RB Symbol | RV TyVar | RP (PVar Type)
data Bind tv pv = RB Symbol | RV tv | RP pv 
  deriving (Data, Typeable)

data RType p c tv pv r
  = RVar !(Bind tv pv) !r
  | RFun !(Bind tv pv) !(RType p c tv pv r) !(RType p c tv pv r)  
  | RAll !(Bind tv pv) !(RType p c tv pv r)
  | RApp !c ![(RType p c tv pv r)] ![r] !r
  | RCls !p ![(RType p c tv pv r)]
  | ROth String
  deriving (Data, Typeable)

class RefTypable a where
  isList :: a -> Bool
  ppCls  :: a -> SDoc

--class RefTypable p c tv pv r where
--  isList    :: c -> Bool
--  pp_class :: p -> [RType p c tv pv r] -> SDoc
--  -- ppr_strip :: RType p c tv pv r -> SDoc

--------------------------------------------------------------------
---------------- Refinement Types: RefType -------------------------
--------------------------------------------------------------------

type RBind = Bind TyVar (PVar Type)

data RTyCon = RTyCon 
  { rTyCon     :: !TC.TyCon         -- GHC Type Constructor
  , rTyConPs   :: ![PVar Type]      -- Predicate Parameters
  }
  deriving (Data, Typeable)

type RefType    = RType Class RTyCon TyVar (PVar Type) (Reft Sort)    

instance Eq RBind where
  RB s == RB s' = s == s'
  RV α == RV α' = α == α'
  RP p == RP p' = pname p == pname p'
  _    == _     = False 

instance Show RefType where
  show = showPpr

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rTyVar α            = RV α
rTyVarSymbol (RV α) = typeUniqueSymbol $ TyVarTy α

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

rPred p t = RAll (RP p) t

addPds ps (RAll v@(RV _) t) = RAll v $ addPds ps t
addPds ps t                 = foldl' (flip rPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2) 
 = (RFun b t1' t2', ps ++ ps1 ++ ps2)
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

strengthenRefType_ (RFun (RB x1) t1 t1') (RFun (RB x2) t2 t2') 
  = RFun (RB x1) t t'
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts = zipWith strengthenRefType_ t1s t2s
          rs = zipWith meet rs1 rs2

strengthenRefType_ t1 _ 
  = t1

-- strengthen  :: RefType -> Reft Sort -> RefType
strengthen (RApp c ts rs r) r' = RApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'       = RVar a      (r `meet` r') 
strengthen t _                 = t 


-- replaceReft  :: RefType -> Reft Sort -> RefType
replaceReft (RApp c ts rs _) r' = RApp c ts rs r' 
replaceReft (RVar a _) r'      = RVar a      r' 
replaceReft t _                = t 


addTyConInfo tyi = mapBot (addTCI tyi) 
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
         ps'  = subsTyVarsP (zip cts τs) <$> ps
         cts  = TC.tyConTyVars c
         rs'  = if (null rs) then ((\_ -> F.trueReft) <$> ps) else rs

-- mkArrow ::  [TyVar] -> [(Symbol, RType a)] -> RType a -> RType a
mkArrow as xts t = mkUnivs as $ mkArrs xts t

mkUnivs αs t  = tr_foldr' RAll t $ RV `fmap` αs
mkArrs xts t = tr_foldr' (\(x,t) -> RFun (RB x) t) t xts

-- bkArrow :: RType a -> ([TyVar], [(Symbol, RType a)],  RType a)
bkArrow ty = (αs, xts, out)
  where (αs, t)    = bkUniv [] ty
        (xts, out) = bkArrs [] t
       

bkUniv αs (RAll (RV α) t) = bkUniv (α : αs) t
bkUniv αs t               = (reverse αs, t)

bkArrs xts (RFun (RB x) t t') = bkArrs ((x,t):xts) t'
bkArrs xts t                  = (reverse xts, t)

rsplitVsPs (RAll (RV v) t) = (v:vs, ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs (RAll (RP p) t) = (vs, p:ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs t = ([], [], t)

rsplitArgsRes (RFun (RB x) t1 t2) = (x:xs, t1:ts, r)
  where (xs, ts, r) = rsplitArgsRes t2
rsplitArgsRes t = ([], [], t)

----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData REnv where
  rnf (REnv m) = () -- rnf m

instance NFData (Bind a b) where
  rnf (RB x) = rnf x
  rnf (RV a) = ()
  rnf (RP p) = () 

instance (NFData a, NFData b, NFData c, NFData d, NFData e) => NFData (RType a b c d e) where
  rnf (RVar α r)       = rnf α `seq` rnf r 
  rnf (RAll α t)       = rnf α `seq` rnf t
  rnf (RFun x t t')    = rnf x `seq` rnf t `seq` rnf t'
  rnf (RApp c ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RCls c ts)      = c `seq` rnf ts
  rnf (ROth _)         = ()

----------------------------------------------------------------
------------------ Printing Refinement Types -------------------
----------------------------------------------------------------

instance (Outputable tv, Outputable pv) => Outputable (Bind tv pv) where
  ppr (RB x) = ppr x
  ppr (RV a) = ppr a
  ppr (RP p) = ppr p

instance Show RBind where
  show = showPpr 

instance RefTypable RefType where
  isList (RApp c _ _ _) = rTyCon c == listTyCon 
  isList _              = False
  ppCls (RCls c ts)     = parens $ pprClassPred c (toType <$> ts)

instance Outputable RefType where
  ppr = ppr_rtype TopPrec

instance Outputable RTyCon where
  ppr (RTyCon c ts) = ppr c -- <+> text "\n<<" <+> hsep (map ppr ts) <+> text ">>\n"
  
instance Show RTyCon where
 show = showPpr

ppr_rtype p (RAll pv@(RP _) t)
  = text "forall" <+> ppr pv <+> ppr_pred p t
ppr_rtype p t@(RAll (RV _) _)       
  = ppr_forall p t
ppr_rtype p (RVar a r)         
  = ppReft r $ ppr a
ppr_rtype p (RFun x t t')  
  = pprArrowChain p $ ppr_dbind x t : ppr_fun_tail t'
ppr_rtype p ty@(RApp c [t] rs r)
  | isList ty -- rTyCon c == listTyCon 
  = ppReft r $ brackets (ppr_rtype p t) <> ppr_tycon_preds rs
ppr_rtype p (RApp c ts rs r)
  = ppReft r $ ppr c <> ppr_tycon_preds rs <+> hsep (ppr_rtype p <$> ts)
ppr_rtype _ ty@(RCls c ts)      
  = ppCls ty -- parens $ pprClassPred c (toType <$> ts)
ppr_rtype _ (ROth s)
  = text "?" <> text s <> text "?"

ppr_pred p (RAll pv@(RP _) t)
  = ppr pv <> ppr_pred p t
ppr_pred p t
  = dot <+> ppr_rtype p t

ppr_class c ts 
  = parens $ pprClassPred c (toType <$> ts)

ppr_tycon_preds rs 
  | all isTautoReft rs 
  = empty
  | otherwise 
  = angleBrackets $ hsep $ punctuate comma $ ppReft_pred <$> rs
  where trivialRefts (Reft (_, ras)) = all isTautoRa ras

ppr_dbind b@(RB x) t 
  | isNonSymbol x 
  = ppr_rtype FunPrec t
  | otherwise
  = braces (ppr b) <> colon <> ppr_rtype FunPrec t

ppr_fun_tail (RFun b t t')  
  = (ppr_dbind b t) : (ppr_fun_tail t')
ppr_fun_tail t
  = [ppr_rtype TopPrec t]

ppr_forall p t
  = maybeParen p FunPrec $ sep [ppr_foralls αs, ppr_rtype TopPrec t']
  where
    (αs,  t')           = split [] t
    split αs (RAll α t) = split (α:αs) t
    split αs t	        = (reverse αs, t)
    ppr_foralls []      = empty
    ppr_foralls αs      = (text "forall") <+> sep (map ppr αs) <> dot


---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

instance Functor (RType a b c d) where
  fmap f (RVar α r)       = RVar α (f r)
  fmap f (RAll a t)       = RAll a (fmap f t)
  fmap f (RFun x t t')    = RFun x (fmap f t) (fmap f t')
  fmap f (RApp c ts rs r) = RApp c (fmap (fmap f) ts) (f <$> rs) (f r)
  fmap f (RCls c ts)      = RCls c (fmap (fmap f) ts)
  fmap f (ROth a)         = ROth a 

subsTyVars_meet   = subsTyVars True
subsTyVars_nomeet = subsTyVars False
subsTyVar_meet    = subsTyVar True
subsTyVar_nomeet  = subsTyVar False

subsTyVars ::  Bool -> [(TyVar, RefType)] -> RefType -> RefType 
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats

subsTyVar ::  Bool -> (TyVar, RefType) -> RefType -> RefType 
subsTyVar meet = subsFree meet S.empty

instance Show Type where
  show  = showSDoc . ppr

subsFree ::  Bool -> S.Set TyVar -> (TyVar, RefType) -> RefType -> RefType

subsFree m s z@(α, t') (RAll (RP p) t)         
  = RAll (RP (subsTyVarsP [(α, toType t')] p)) $ subsFree m s z t
subsFree m s z (RAll (RV α) t)         
  = RAll (RV α) $ subsFree m (α `S.insert` s) z t
subsFree m s z (RFun x t t')       
  = RFun x (subsFree m s z t) (subsFree m s z t') 
subsFree m s z@(α, t') t@(RApp c ts rs r)     
  = RApp c' (subsFree m s z <$> ts) rs r  
    where c' = c {rTyConPs = (subsTyVarsP [(α, toType t')]) <$> (rTyConPs c)}
    -- UNIFY: why instantiating INSIDE parameters?
subsFree m s z (RCls c ts)     
  = RCls c (subsFree m s z <$> ts)
subsFree meet s (α', t') t@(RVar (RV α) r) 
  | α == α' && α `S.notMember` s 
  = if meet then t' `strengthen` r else t' 
  | otherwise
  = t
subsFree _ _ _ t@(ROth _)        
  = t


---------------------------------------------------------------

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RApp _ _ _ x)   
  = Just x
stripRTypeBase (RVar _ x)   
  = Just x
stripRTypeBase _                
  = Nothing


ofType :: Type -> RefType
ofType τ = --traceShow ("ofType τ = " ++ showPpr τ) $ 
           ofType_ τ

ofType_ :: Type -> RefType 
ofType_ (FunTy τ τ')    
  = RFun (RB dummySymbol) (ofType_ τ) (ofType_ τ')
ofType_ (ForAllTy α τ)  
  = RAll (rTyVar α) $ ofType_ τ  
ofType_ (TyVarTy α)     
  = RVar (rTyVar α) trueReft 
ofType_ τ
  | isPredTy τ
  = ofPredTree (classifyPredType τ)  
ofType_ τ@(TyConApp c _)
  | TC.isSynTyCon c
  = ofSynTyConApp τ
  | otherwise
  = ofTyConApp τ
ofType_ τ               
  = ROth (show τ)  

ofPredTree (ClassPred c τs)
  = RCls c (ofType_ <$> τs)
 

ofTyConApp  τ@(TyConApp c τs) 
  = RApp (RTyCon c []) (ofType_ <$> τs) [] trueReft

ofSynTyConApp (TyConApp c τs) 
  = ofType_ $ substTyWith αs τs τ
  where (αs, τ) = TC.synTyConDefn c

-----------------------------------------------------------------
---------------------- Scrap this using SYB? --------------------
-----------------------------------------------------------------

mapTop ::  (RefType -> RefType) -> RefType -> RefType
mapTop f t = 
  case f t of
    (RAll a t')      -> RAll a (mapTop f t')
    (RFun x t' t'')  -> RFun x (mapTop f t') (mapTop f t'')
    (RApp c ts rs r) -> RApp c (mapTop f <$> ts) rs r
    (RCls c ts)      -> RCls c (mapTop f <$> ts)
    t'               -> t' 

mapBot ::  (RefType -> RefType) -> RefType -> RefType
mapBot f (RAll a t)       = RAll a (mapBot f t)
mapBot f (RFun x t t')    = RFun x (mapBot f t) (mapBot f t')
mapBot f (RApp c ts rs r) = f $ RApp c (mapBot f <$> ts) rs r
mapBot f (RCls c ts)      = RCls c (mapBot f <$> ts)
mapBot f t'               = f t' 

canonRefType :: RefType -> RefType
canonRefType = mapTop zz
  where zz t@(RApp c ts rs r)  = RApp c ts (map canonReft rs) (canonReft r)
        zz t                      = t

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

--tidyTyVars' r = traceShow ("tidyTyVars: " ++ show r) $ tidyTyVars r 

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
--mkSymbol v = S $ vs ++ [symSep] ++ us
--  where us  = showPpr $ getUnique v 
--        vs  = pprShort v
--
--mkSymbol v = traceShow ("mkSymbol " ++ showPpr v ++ " = ") $ mkSymbol' v

mkSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSep] ++ us
  where us  = showPpr $ getUnique v 
        vs  = pprShort v

dataConSymbol = mkSymbol . dataConWorkId

primOrderingSort = typeSort $ dataConRepType eqDataCon
ordCon s = EDat (S s) primOrderingSort

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

dropModuleNames = last . words . (dotWhite <$>) 
  where dotWhite '.' = ' '
        dotWhite c   = c

---------------------------------------------------------------
---------------------- Embedding RefTypes ---------------------
---------------------------------------------------------------

-- toType :: RType t -> Type
toType (RFun _ t t')   
  = FunTy (toType t) (toType t')
toType (RAll (RV α) t)      
  = ForAllTy α (toType t)
toType (RVar (RV α) _)        
  = TyVarTy α
toType (RApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
toType (RCls c ts)   
  = predTreePredType $ ClassPred c (toType <$> ts)
  -- = PredTy (ClassP c (toType <$> ts))
toType (ROth t)      
  = errorstar $ "toType fails: " ++ t

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
  = FPtr $ FLoc $ typeUniqueSymbol τ
typeSortFun τ1 τ2
  = FFunc n $ genArgSorts sos
  where sos  = typeSort <$> τs
        τs   = τ1  : grabArgs [] τ2
        n    = (length sos) - 1
     
typeUniqueSymbol :: Type -> Symbol 
typeUniqueSymbol = stringSymbol . ("sort_" ++) . showSDocDump . ppr

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

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α) x       
  = RVar (rTyVar α) x 
makeRTypeBase τ@(TyConApp c _) x 
  = RApp (RTyCon c []) [] [] x

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

-- refTypePredSortedReft_   :: (Reft, Type) -> SortedReft
refTypePredSortedReft_ (r, τ) = RR so r
  where so = typeSort τ
refTypePredSortedReft r = RR so r
  where so = FObj -- typeSort τ

refTypeSortedReft   ::  RefType -> SortedReft
refTypeSortedReft t = RR so r
  where so = {- traceShow ("rTypeSort: t = " ++ showPpr t) $ -} rTypeSort t
        r  = fromMaybe trueReft $ stripRTypeBase t 

-- typeSortedReft ::  Type -> Refa -> SortedReft
typeSortedReft t r = RR so $ Reft(vv,[r])
  where so = typeSort t


-- rTypeSort ::  RType t -> Sort
rTypeSort = typeSort . toType



-------------------------------------------------------------------
-------------------------- Substitution ---------------------------
-------------------------------------------------------------------

instance Subable RefType  where
  subst = fmap . subst 

