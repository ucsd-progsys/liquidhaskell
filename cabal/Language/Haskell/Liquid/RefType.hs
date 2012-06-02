{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, DeriveDataTypeable, RankNTypes, GADTs #-}


{- Refinement Types Mirroring the GHC Type definition -}

module Language.Haskell.Liquid.RefType (
    RType (..), RTyCon(..)
  , RefType (..)  
  , RBind (..), RTyVar
  , ofType, toType
  , rTyVar, rTyVarSymbol
  , typeId
  , strengthen, strengthenRefType
  , mkArrow, normalizePds, rsplitVsPs, rsplitArgsRes
  , subsTyVar_meet, subsTyVars_meet, subsTyVar_nomeet, subsTyVars_nomeet
  , stripRTypeBase, refTypePredSortedReft_,refTypeSortedReft, typeSortedReft, refTypePredSortedReft, rTypeSort
  , canonRefType, tidyRefType
  , mkSymbol, dataConSymbol, dataConMsReft, dataConReft  
  , literalRefType, literalConst
  , REnv, deleteREnv, domREnv, insertREnv, lookupREnv, emptyREnv, memberREnv, fromListREnv
  , toTyVar, addTyConInfo
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
---------------------- Refinement Types ----------------------------
--------------------------------------------------------------------

newtype TyId 
  = TI String deriving (Eq, Ord, Show, Data, Typeable)

typeId :: TC.TyCon -> TyId
typeId = TI . showPpr

newtype RBind = RB Symbol
  deriving (Data, Typeable)

newtype RTyVar = RT (TyVar, Symbol)
  deriving (Eq, Ord, Data, Typeable)

data RTyCon = RTyCon { rTyCon     :: !TC.TyCon
                     , rTyConPs   :: ![Predicate]
                     }
  deriving (Data, Typeable)

data RType a 
  = RVar    !RTyVar    !a
  | RFun    !RBind     !(RType a)  !(RType a)
  | RAll    !RTyVar    !(RType a)
  | RConApp !RTyCon    ![RType a]  ![a]       !a
  | RClass  !Class     ![RType a]
  | RPred   !Predicate !(RType a)
  | ROther  !Type 
  deriving (Data, Typeable)

type RefType    = RType Reft    

instance Show RefType where
  show = showPpr

--------------------------------------------------------------------
---------------------- Helper Functions ----------------------------
--------------------------------------------------------------------

rTyVar α = RT (α, mkSymbol α)
rTyVarSymbol (RT (α, _)) = typeUniqueSymbol $ TyVarTy α

normalizePds t = addPds ps t'
  where (t', ps) = nlzP [] t

addPds ps (RAll v t) = RAll v $ addPds ps t
addPds ps t          = foldl' (flip RPred) t ps

nlzP ps t@(RVar _ _ ) 
 = (t, ps)
nlzP ps (RFun b t1 t2) 
 = (RFun b t1' t2', ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAll v t )
 = (RAll v t', ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(RConApp c ts rs r)
 = (t, ps)
nlzP ps t@(RClass c ts)
 = (t, ps)
nlzP ps (RPred p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@(ROther τ)
 = (t, ps)

toTyVar (RT(v, _)) = v

strengthenRefType :: RefType -> RefType -> RefType
strengthenRefType t1 t2 
  | eqt t1 t2 
  = strengthenRefType_ t1 t2
  | otherwise
  = errorstar $ "strengthen on differently shaped reftypes! " 
              ++ "t1 = " ++ showPpr t1 
              ++ "t2 = " ++ showPpr t2
  where eqt t1 t2 = showPpr (toType t1) == showPpr (toType t2)
  
strengthenRefType_ (RAll a t1) (RAll _ t2)
  = RAll a $ strengthenRefType_ t1 t2

strengthenRefType_ (RFun (RB x1) t1 t1') (RFun (RB x2) t2 t2') 
  = RFun (RB x1) t t'
    where t  = strengthenRefType_ t1 t2
          t' = strengthenRefType_ t1' $ subst1 t2' (x2, EVar x1)

strengthenRefType_ (RConApp tid t1s rs1 r1) (RConApp _ t2s rs2 r2)
  = RConApp tid ts rs (r1 `meet` r2)
    where ts = zipWith strengthenRefType_ t1s t2s
          rs = zipWith meet rs1 rs2

strengthenRefType_ t1 _ 
  = t1

strengthen  :: RefType -> Reft -> RefType
strengthen (RConApp c ts rs r) r' = RConApp c ts rs (r `meet` r') 
strengthen (RVar a r) r'      = RVar a      (r `meet` r') 
strengthen t _                = t 


replaceReft  :: RefType -> Reft -> RefType
replaceReft (RConApp c ts rs _) r' = RConApp c ts rs r' 
replaceReft (RVar a _) r'      = RVar a      r' 
replaceReft t _                = t 



addTyConInfo tyi = mapBot (addTCI tyi) 
addTCI tyi t@(RConApp c ts rs r)
  = case (M.lookup (rTyCon c) tyi) of
     Just c' -> rConApp c' ts rs r
     Nothing -> rConApp c  ts rs r
addTCI _ t
  = t

showTy v = showSDoc $ ppr v <> ppr (varUnique v)
-- showTy t = showSDoc $ ppr t

rConApp (RTyCon c ps) ts rs r = RConApp (RTyCon c ps') ts rs' r 
   where τs   = toType <$> ts
         ps'  = subsTyVarsP (zip cts τs) <$> ps
         cts  = TC.tyConTyVars c
         rs'  = if (null rs) then ((\_ -> F.trueReft) <$> ps) else rs
         

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

rsplitVsPs (RAll v t) = (v:vs, ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs (RPred p t) = (vs, p:ps, t')
  where (vs, ps, t') = rsplitVsPs t
rsplitVsPs t = ([], [], t)

rsplitArgsRes (RFun (RB x) t1 t2) = (x:xs, t1:ts, r)
  where (xs, ts, r) = rsplitArgsRes t2
rsplitArgsRes t = ([], [], t)

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

{-
instance (NFData a) => NFData (RTyCon a) where
  rnf (RAlgTyCon x1 x2) = x1 `seq` rnf x2 
  rnf (RPrimTyCon x)    = x `seq` () 

instance (NFData a) => NFData (RAlgRhs a) where
  rnf (RDataTyCon x1 x2) = rnf x1 `seq` rnf x2 

instance (NFData a) => NFData (RDataCon a) where
  rnf (MkRData x1 x2)    = x1 `seq` rnf x2
-}

instance (NFData a) => NFData (RType a) where
  rnf (RPred p t)     = rnf p `seq` rnf t
  rnf (RVar α r)      = rnf α `seq` rnf r 
  rnf (RAll α t)      = rnf α `seq` rnf t
  rnf (RFun x t t')   = rnf x `seq` rnf t `seq` rnf t'
  rnf (RConApp c ts rs r) = rnf ts `seq` rnf rs `seq` rnf r
  rnf (RClass c ts)   = c `seq` rnf ts
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

instance Outputable RTyCon where
 ppr (RTyCon c ts) = ppr c <+> text "\n<<" <+> hsep (map ppr ts) <+> text ">>\n"

instance Show RTyCon where
 show = showPpr

instance Outputable Reft where
  ppr = text . show
brance x = char '[' <> ppr x <> char ']'

ppr_reftype p (RPred pr t)
  = text "forall" <+> ppr pr <+> ppr_pred p t
ppr_reftype p (RVar a r)         
  = ppReft r $ ppr a
ppr_reftype p (RFun x t t')      
  = pprArrowChain p $ ppr_dbind x t : ppr_fun_tail t'
ppr_reftype p t@(RAll _ _)       
  = ppr_forall_reftype p t
ppr_reftype p (RConApp c ts rs r)
  = ppr c <+> ppr_tyConTy p c ts<+> text "\n"<> braces (hsep (map ppr rs)) <+> ppr r

ppr_reftype _ (RClass c ts)      
  = parens $ pprClassPred c (toType <$> ts)
ppr_reftype _ (ROther t)         
  = text "?" <> ppr t <> text "?"

ppr_tyConTy p (RTyCon _ _) ts  = braces (hsep (map (ppr_reftype p) ts)) 

ppr_pred p (RPred pr t)
  = ppr pr <> ppr_pred p t
ppr_pred p t
  = char '.' <+> ppr_reftype p t


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

instance Functor RType where
  fmap f (RPred p r)     = RPred p (fmap f r)
  fmap f (RVar α r)      = RVar α (f r)
  fmap f (RAll a t)      = RAll a (fmap f t)
  fmap f (RFun x t t')   = RFun x (fmap f t) (fmap f t')
  fmap f (RConApp c ts rs r) = RConApp c (fmap (fmap f) ts) (f <$> rs) (f r)
  fmap f (RClass c ts)   = RClass c (fmap (fmap f) ts)
  fmap f (ROther a)      = ROther a 

subsTyVars_meet   = subsTyVars True
subsTyVars_nomeet = subsTyVars False
subsTyVar_meet    = subsTyVar True
subsTyVar_nomeet  = subsTyVar False

subsTyVars ::  Bool -> [(RTyVar, RefType)] -> RefType -> RefType 
subsTyVars meet ats t = foldl' (flip (subsTyVar meet)) t ats


subsTyVar ::  Bool -> (RTyVar, RefType) -> RefType -> RefType 
subsTyVar meet = subsFree meet S.empty
instance Show Type where
  show  = showSDoc . ppr
subsFree ::  Bool -> S.Set RTyVar -> (RTyVar, RefType) -> RefType -> RefType
subsFree m s z (RPred p t)         
  = RPred (subsTyVarP z' p) $ subsFree m s z t
   where (RT (v, _), tv) = z
         z'             = (v, toType tv)
subsFree m s z (RAll α' t)         
  = RAll α' $ subsFree m (α' `S.insert` s) z t
subsFree m s z (RFun x t t')       
  = RFun x (subsFree m s z t) (subsFree m s z t') 
subsFree m s z t@(RConApp c ts rs r)     
 = RConApp (c{rTyConPs = (subsTyVarP z') <$> (rTyConPs c)}) (subsFree m s z <$> ts) rs r  
    where (RT (v, _), tv) = z
          z'             = (v, toType tv)
subsFree m s z (RClass c ts)     
  = RClass c (subsFree m s z <$> ts)
subsFree meet s (α', t') t@(RVar α r) 
  | α == α' && α `S.notMember` s 
  = if meet then t' `strengthen` r else t' 
  | otherwise
  = t
subsFree _ _ _ t@(ROther _)        
  = t


---------------------------------------------------------------

stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RConApp _ _ _ x)   
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
--  | TC.isPrimTyCon c   
--  = ofPrimTyConApp s τ
--  | TC.isAlgTyCon c 
--  = ofAlgTyConApp s τ
  | TC.isSynTyCon c
  = ofSynTyConApp s τ
  | otherwise
  = ofTyConApp s τ
ofType_ _ τ               
  = ROther τ  

ofPredTree s (ClassPred c τs)
  = RClass c (ofType_ s <$> τs)
 

ofTyConApp s τ@(TyConApp c τs) 
  = RConApp (RTyCon c []) ts [] trueReft --undefined
  where ts  = ofType_ s <$> τs

ofSynTyConApp s (TyConApp c τs) 
  = ofType_ s $ substTyWith αs τs τ
  where (αs, τ) = TC.synTyConDefn c

-----------------------------------------------------------------
---------------------- Scrap this using SYB? --------------------
-----------------------------------------------------------------

mapTop ::  (RefType -> RefType) -> RefType -> RefType
mapTop f t = 
  case f t of
    (RAll a t')         -> RAll a (mapTop f t')
    (RPred p t')        -> RPred p (mapTop f t')
    (RFun x t' t'')     -> RFun x (mapTop f t') (mapTop f t'')
    (RConApp c ts rs r) -> RConApp c (mapTop f <$> ts) rs r
    (RClass c ts)       -> RClass c (mapTop f <$> ts)
    t'                  -> t' 

mapBot ::  (RefType -> RefType) -> RefType -> RefType
mapBot f (RAll a t)          = RAll a (mapBot f t)
mapBot f (RPred p t)         = RPred p (mapBot f t)
mapBot f (RFun x t t')       = RFun x (mapBot f t) (mapBot f t')
mapBot f (RConApp c ts rs r) = f $ RConApp c (mapBot f <$> ts) rs r
mapBot f (RClass c ts)       = RClass c (mapBot f <$> ts)
mapBot f t'                  = f t' 

canonRefType :: RefType -> RefType
canonRefType = mapTop zz
  where zz t@(RConApp c ts rs r)  = RConApp c ts (map canonReft rs) (canonReft r)
        zz t                      = t

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
  where getS (RT (_, x))   = Just (symbolString x)
        putS (RT (α, _)) x = RT (stringTyVar x, stringSymbol x) 
        pool               = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]

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
{-
dropFix s 
  | fixS `isPrefixOf` s
  = dropFix $ drop l s
  | otherwise 
  = s
  where fixS = "fix" ++ [symSep]
        l    = length fixS
-}

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

dataConReft   ::  DataCon -> Type -> Reft 
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

toType :: RType t -> Type
toType (RFun _ t t')   
  = FunTy (toType t) (toType t')
toType (RAll (RT (α,_))  t)      
  = ForAllTy α (toType t)
toType (RVar (RT (α,_)) _)        
  = TyVarTy α
toType (RConApp (RTyCon {rTyCon = c}) ts _ _)   
  = TyConApp c (toType <$> ts)
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

makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α) x       
  = RVar (rTyVar α) x 
makeRTypeBase τ@(TyConApp c _) x 
  = RConApp (RTyCon c []) [] [] x

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
    where pprxt (x, t) = ppr x <> text " :: " <> ppr t  

refTypePredSortedReft_   :: (Reft, Type) -> SortedReft
refTypePredSortedReft_ (r, τ) = RR so r
  where so = typeSort τ
refTypePredSortedReft r = RR so r
  where so = FObj -- typeSort τ

refTypeSortedReft   ::  RType Reft -> SortedReft
refTypeSortedReft t = RR so r
  where so = {- traceShow ("rTypeSort: t = " ++ showPpr t) $ -} rTypeSort t
        r  = fromMaybe trueReft $ stripRTypeBase t 

typeSortedReft ::  Type -> Refa -> SortedReft
typeSortedReft t r = RR so $ Reft(vv,[r])
  where so = typeSort t


rTypeSort ::  RType t -> Sort
rTypeSort = typeSort . toType



-------------------------------------------------------------------
-------------------------- Substitution ---------------------------
-------------------------------------------------------------------

instance Subable RefType  where
  subst = fmap . subst 

