{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Language.Haskell.Liquid.PredType (
								  PrTy (..),  PrType (..), ofTypeP
								, Predicate (..), pand
								, TyConP (..), DataConP (..)
								, PEnv (..), lookupPEnv, fromListPEnv, insertPEnv, emptyPEnv, mapPEnv
								, splitVsPs, typeAbsVsPs, splitArgsRes
								, generalize, generalizeArgs
								, subp, subsTyVars, substSym, subsTyVarsP, subsTyVars_
								, dataConTy, dataConPtoPredTy
								, removeExtPreds
								) where

import Class
import CoreSyn
import Type
import TcType
import TypeRep
import qualified TyCon as TC
import Literal
import Class
import Var 
import Unique (getUnique)

import Outputable hiding (empty)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import Data.List  (foldl')
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint

import Control.Applicative  ((<$>))
import Control.DeepSeq
import Data.Data

data Predicate t 
  = PdVar (PVar t) -- {pname :: !String, ptype :: !t, pargs :: ![(t, Symbol, Symbol)]}
  | PdTrue
  | (Predicate t) `PdAnd` (Predicate t)
    deriving (Data, Typeable)

-- type Predicate = Predicate_ Type

data PrTy a = PrVar   !TyVar     !a
            | PrLit   !Literal   !a
      		| PrAll   !TyVar     !(PrTy a)
      		| PrAllPr !a         !(PrTy a)
      		| PrClass !Class     ![PrTy a]
      		| PrFun   !Symbol    !(PrTy a)   !(PrTy a)
      		| PrTyCon !TC.TyCon  ![PrTy a]   ![a] !a
            deriving (Data, Typeable)


instance Functor Predicate where
  fmap f (PdVar v)      = PdVar (fmap f v)
  fmap f PdTrue         = PdTrue
  fmap f (p `PdAnd` p') = (fmap f p) `PdAnd` (fmap f p')

type PrType = PrTy (Predicate Type)

data TyConP = TyConP { freeTyVarsTy :: ![TyVar]
                     , freePredTy   :: ![(Predicate Type)]
                     }

data DataConP = DataConP { freeTyVars :: ![TyVar]
                         , freePred   :: ![(Predicate Type)]
                         , tyArgs     :: ![(Symbol, PrType)]
                         , tyRes      :: !PrType
                         }

dataConPtoPredTy :: DataConP -> PrType
dataConPtoPredTy (DataConP vs ps yts rt) = t3						
  where t1 = foldl' (\t2 (x, t1) -> PrFun x t1 t2) rt yts 
        t2 = foldl' (\t p -> PrAllPr p t) t1 (reverse ps) 
        t3 = foldl' (\t v -> PrAll v t) t2 (reverse vs)


instance Outputable TyConP where
 ppr (TyConP vs ps) 
   = (parens $ hsep (punctuate comma (map ppr vs))) <+>
     (parens $ hsep (punctuate comma (map ppr ps)))

instance Show TyConP where
 show = showSDoc . ppr

instance Outputable DataConP where
 ppr (DataConP vs ps yts t) 
   = (parens $ hsep (punctuate comma (map ppr vs))) <+>
     (parens $ hsep (punctuate comma (map ppr ps))) <+>
     (parens $ hsep (punctuate comma (map ppr yts))) <+>
     ppr t

instance Show DataConP where
 show = showSDoc . ppr

removeExtPreds t@(PrAll _ _) = t
removeExtPreds (PrAllPr p t) = removeExtPreds (subp (M.singleton p PdTrue) t) 
removeExtPreds t             = t

dataConTy m (TyVarTy v)            
  = M.findWithDefault (PrVar v PdTrue) v m
dataConTy m (FunTy t1 t2)          
  = PrFun dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy c t)          
  = PrAll c (dataConTy m t)
dataConTy m t
  | isPredTy t
  = ofPredTree $ classifyPredType t
dataConTy m (TyConApp c ts)        
  = PrTyCon c (map (dataConTy m) ts) [] PdTrue
dataConTy _ t
	= error "ofTypePAppTy"


ofTypeP (TyVarTy v)            
  = PrVar v PdTrue
ofTypeP (FunTy t1 t2)          
  = PrFun dummySymbol (ofTypeP t1) (ofTypeP t2)
ofTypeP (ForAllTy c t)          
  = PrAll c (ofTypeP t)
ofTypeP t
  | isPredTy t
  = ofPredTree $ classifyPredType t
ofTypeP (TyConApp c ts)
  | TC.isSynTyCon c
  = ofTypeP $ substTyWith αs ts τ
  | otherwise
  = PrTyCon c (map ofTypeP ts) [] PdTrue
 where (αs, τ) = TC.synTyConDefn c
ofTypeP t
	= error "ofTypePAppTy"

ofPredTree (ClassPred c ts)
  = PrClass c (map ofTypeP ts)
ofPredTree _
  = error "ofPredTree"

generalize     = generalize_ freePreds
generalizeArgs = generalize_ freeArgPreds

generalize_ f t = typeAbsVsPs t' vs ps
  where (vs, ps', t') = splitVsPs t
        ps            = (S.toList (f t)) ++ ps'

freeArgPreds (PrFun _ t1 t2) = freePreds t1
freeArgPreds (PrAll _ t)     = freeArgPreds t
freeArgPreds (PrAllPr _ t)   = freeArgPreds t
freeArgPreds t               = freePreds t

freePreds :: PrType -> S.Set (Predicate Type)
freePreds (PrVar _ p) = S.fromList $ normalizeP p
freePreds (PrLit _ p) = S.fromList $ normalizeP p
freePreds (PrAll _ t) = freePreds t
freePreds (PrAllPr p t) = S.delete p $ freePreds t 
freePreds (PrClass _ ts) = foldl' (\z t -> S.union z (freePreds t)) S.empty ts
freePreds (PrFun _ t1 t2) = S.union (freePreds t1) (freePreds t2)
freePreds (PrTyCon _ ts ps p) = foldl' (\z t -> S.union z (freePreds t)) pps ts
  where pps = S.fromList $ concatMap normalizeP (p:ps)

normalizeP p@(PdVar _)   = [p]
normalizeP (PdAnd p1 p2) = normalizeP p1 ++ normalizeP p2
normalizeP _             = []

pand PdTrue (PdAnd p1 p2) = pand p1 p2
pand PdTrue p             = p
pand p     (PdAnd p1 p2)  = PdAnd p $ pand p1 p2
pand p     PdTrue         = p
pand p     q              = PdAnd p q

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy t = showSDoc $ ppr t

subsTyVarsP ::  Functor f => [(Var, Type)] -> f Type -> f Type
subsTyVarsP vts p = foldl' (flip subsTyVarP) p vts 
  where subsTyVarP = fmap . tvSubst

tvSubst (v, t) t'@(TyVarTy v') 
  | eqTv v v' = t
  | otherwise = t'

eqTv α α' = tvId α == tvId α'
  where tvId α = show α ++ show (varUnique α)
 
subsTyVar :: (Var, PrTy (Predicate Type)) -> PrTy (Predicate Type) -> PrTy (Predicate Type)
subsTyVar (α, (PrVar a' p')) t@(PrVar a p) 
  | α `eqTv` a 
  = PrVar a' (pand p p')
  | otherwise
  = t
subsTyVar (α, (PrLit l p')) t@(PrVar a p) 
  | α `eqTv` a
  = PrLit l (pand p p')
  | otherwise 
  = t
subsTyVar (α, (PrTyCon c ts ps p')) t@(PrVar a p)
  | α `eqTv` a 
  = PrTyCon c ts ps (pand p p')
  | otherwise 
  = t
subsTyVar (α, τ) t@(PrVar a p) 
  | α `eqTv` a 
  = τ 
  | otherwise 
  = t       

subsTyVars_ (v, t, τ) = fmap (subsTyVarsP [(v, τ)]) . mapTyVar (subsTyVar (v, t))
subsTyVars s = fmap (subsTyVarP_ s) . mapTyVar (subsTyVar s)

subsTyVarP_ av@(α, (PrVar a' p')) p@(PdVar (PV n (TyVarTy v) a))
  | α `eqTv` v 
  = PdVar (PV n (TyVarTy a') ((subsTyVarAP_ av) <$> a))
  | otherwise
  = PdVar (PV n (TyVarTy v) ((subsTyVarAP_ av) <$> a))
subsTyVarP_ z (PdAnd p1 p2)
  = PdAnd (subsTyVarP_ z p1) (subsTyVarP_ z p2)
subsTyVarP_ _ p 
  = p
subsTyVarAP_ (α, (PrVar a' p')) (TyVarTy v, x1, x2)
  | α `eqTv` v 
  = (TyVarTy a', x1, x2)
subsTyVarAP_ (α, (PrVar a' p')) a
  = a



substSym (x, y) = mapSymbol $ \s -> if (s == x) then y else s

mapTyVar ::  (PrTy a -> PrTy a) -> PrTy a -> PrTy a
mapTyVar  f = mapTy (id, f)
mapSymbol f = fmap (mapPd f) .  mapTy (f, id)
-- substSymP = mapPd substSym

mapPd f (PdVar (PV n t a)) = PdVar (PV n t ((mapThd3 f) <$> a))
mapPd _ PdTrue             = PdTrue
mapPd f (p1 `PdAnd` p2)    = (mapPd f p1) `PdAnd` (mapPd f p2)  

mapTy ::  (Symbol -> Symbol, PrTy a -> PrTy a) -> PrTy a -> PrTy a
mapTy f@(fs, _) (PrFun s t1 t2) = PrFun (fs s) (mapTy f t1) (mapTy f t2)
mapTy f (PrAll a t)             = PrAll a (mapTy f t)
mapTy f (PrAllPr p t)           = PrAllPr p (mapTy f t)
mapTy f (PrLit l p)             = PrLit l p
mapTy (_, fv) t@(PrVar a p)     = fv t
mapTy f (PrTyCon c ts ps p)     = PrTyCon c ((mapTy f) <$> ts) ps p
mapTy f (PrClass c ts)          = PrClass c (mapTy f <$> ts)

lookupP p@(PdVar (PV _ _ s')) s
 = case (L.lookup p (M.toList s)) of 
    Nothing -> p
    Just q  -> addS s' q
lookupP p s
 = case (L.lookup p (M.toList s)) of 
    Nothing -> p
    Just q  -> q
addS s (PdVar (PV n t _)) = PdVar (PV n t s)
addS s PdTrue        = PdTrue
addS s (PdAnd p1 p2 ) = PdAnd (addS s p1) (addS s p2)

class SubstP a where
  subp :: M.Map (Predicate Type) (Predicate Type) -> a -> a

instance SubstP (Predicate Type) where
  subp s p@(PdVar (PV e t a)) = lookupP p s -- not correct!
  subp _ PdTrue               = PdTrue
  subp s (PdAnd p1 p2)        = PdAnd (subp s p1) (subp s p2)


instance SubstP (PrTy (Predicate Type)) where
  subp s t = fmap (subp s) t

typeAbsVsPs t vs ps
  = foldl' (flip PrAll) (foldl' (flip PrAllPr) t ps) (reverse vs)

splitVsPs (PrAll v t) = (v:vs, ps, t')
  where (vs, ps, t') = splitVsPs t
splitVsPs (PrAllPr p t) = (vs, p:ps, t')
  where (vs, ps, t') = splitVsPs t
splitVsPs t           = ([], [], t)

splitArgsRes (PrFun _ t1 t2) = (t1:t1', t2')
  where (t1', t2') = splitArgsRes t2
	
splitArgsRes t = ([], t)


data PEnv = PEnv (M.Map Symbol PrType)
				    deriving (Data, Typeable)

lookupPEnv :: Symbol -> PEnv -> Maybe PrType
lookupPEnv x (PEnv e) = M.lookup x e
emptyPEnv = PEnv M.empty
mapPEnv f (PEnv m) = PEnv $ M.map f m
insertPEnv (x, t) (PEnv e) = PEnv $ M.insert x t e
fromListPEnv = PEnv . M.fromList

instance Eq (Predicate a) where
 (PdVar (PV s1 _ _)) == (PdVar (PV s2 _ _))  
   = s1 == s2
 (PdVar _) == _               
   = False
 PdTrue  == PdTrue          
   = True
 PdTrue  ==  _               
   = False
 (PdAnd p11 p12) == (PdAnd p21 p22)
   = p11 == p21 && p12 == p22
 (PdAnd p11 p12) == _
   = False


instance Ord (Predicate a) where
 compare (PdVar (PV s1 _ _)) (PdVar (PV s2 _ _))  
   = compare s1 s2
 compare (PdVar (PV s  _ _)) _               
   = GT
 compare PdTrue         PdTrue          
   = EQ
 compare PdTrue         _               
   = LT
 compare (PdAnd p11 p12) (PdAnd p21 p22)
   | q== EQ
	 = compare p12 p22
	 | otherwise
	 = q
	 where q = compare p11 p21 
 compare (PdAnd _ _) _ 
  = LT

instance Outputable (PVar Type) where
  ppr  = ppr_pvar (ppr . varUnique)

ppr_pvar pprv (PV s (TyVarTy v) []) = ppr s <> colon <> ppr v <> pprv v
ppr_pvar pprv (PV s t [])           = ppr s <> colon <> ppr t
ppr_pvar pprv (PV s t xs)           = ppr (PdVar (PV s t [])) <+> (parens $ hsep (punctuate comma (map (pprArgs pprv) xs)))


pprArgs pprv (TyVarTy v, x1, x2) = parens $ ppr x2 <> text " : " <> ppr v <> pprv v
pprArgs _    (t        , x1, x2) = parens $ ppr t <> text " : " <> ppr x2

instance Show (Predicate Type) where
  show = showSDoc . ppr

instance Outputable (Predicate Type) where
  ppr (PdVar pv)    = ppr pv
  ppr PdTrue        = text "True"
  ppr (PdAnd p1 p2) = ppr p1 <+> text "&" <+> ppr p2

instance Functor PrTy where
 fmap f (PrFun s t1 t2)     = PrFun s (fmap f t1) (fmap f t2)
 fmap f (PrAll a t)         = PrAll a (fmap f t)
 fmap f (PrAllPr p t)       = PrAllPr (f p) (fmap f t)
 fmap f (PrLit l p)         = PrLit l (f p)
 fmap f (PrVar a p)         = PrVar a (f p)
 fmap f (PrTyCon c ts ps p) = PrTyCon c ((fmap f) <$> ts) (f <$> ps) (f p)
 fmap f (PrClass c ts)      = PrClass c (fmap f <$> ts)


instance Outputable PrType where
 ppr t@(PrFun s t1 t2)   = ppr_fun t
 ppr (PrAll a t)         = text "forall" <+> ppr a <+> ppr_forall t
 ppr (PrAllPr p t)       = text "forall" <+> ppr p <+> ppr_forall t
 ppr (PrLit l p)         = ppr l <+> ppr p
 ppr (PrVar a p)         = ppr a <+>  ppr p
 ppr (PrTyCon c ts ps p) = ppr c <+> braces (hsep (map ppr ts)) <+> braces (hsep (map ppr ps)) <+> ppr p
 ppr (PrClass c ts)    = ppr c <+> (braces $ hsep (map ppr ts))

ppr_forall (PrAll v t)   = ppr v <> ppr (varUnique v)<+> ppr_forall t
ppr_forall (PrAllPr p t) = ppr p <+> ppr_forall t
ppr_forall t             = dot  <> ppr t

ppr_fun (PrFun s t1 t2)  = ppr_fun_l (s, t1) <+> ppr t2 
ppr_fun t                = ppr t

brance x = char '[' <> ppr x <> char ']'

ppr_fun_l (_, PrClass c ts) 
  = ppr c <+> (braces $ hsep (map ppr ts)) <+> text "=>"
ppr_fun_l (s, PrFun s1 t1 t2) 
  = ppr s <> char ':'
          <> (parens (ppr_fun_l (s1, t1) <> ppr t2)) 
		        <+> text "->"
ppr_fun_l (s, t) 
  = ppr s <> char ':' <> ppr t <+> text "->"

instance Outputable PEnv where
 ppr (PEnv e) = vcat $ map pprxt $ M.toAscList e
	  where pprxt (x, t) = ppr x <+> text "::" <+> ppr t

instance Show PEnv where
 show = showSDoc . ppr


instance Show PrType where
 show = showSDoc . ppr

instance NFData PEnv where
  rnf (PEnv e) = ()

instance NFData (Predicate a) where
  rnf _ = ()

instance NFData PrType where
  rnf _ = ()
