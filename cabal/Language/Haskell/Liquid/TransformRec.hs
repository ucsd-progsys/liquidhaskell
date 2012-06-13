{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}

module Language.Haskell.Liquid.TransformRec (
     transformRecExpr
     ) where
import Outputable
import CoreUtils (exprType)
import MkCore (mkCoreLams)
import Var
import Coercion
import Type (mkForAllTys)
import TypeRep
import Unique hiding (deriveUnique)
import CoreSyn
import qualified Data.Map as M
import Language.Haskell.Liquid.Misc
import CoreLint
import Bag
import ErrUtils
import SrcLoc
import OccName
import Name

import Control.Monad.State


transformRecExpr :: CoreProgram -> CoreProgram
transformRecExpr cbs
  =  if (isEmptyBag e) then {-trace "new cbs"-} pg else error (showPpr pg ++ "Type-check" ++ show e)
  where pg     = scopeTr $ evalState (transPg cbs) initEnv
        (w, e) = lintCoreBindings pg


scopeTr = outerScTr . map innerScTr

outerScTr []                  = []
outerScTr ((NonRec x ex):xes) = (NonRec x ex):(mkOuterScTr x [] xes)
outerScTr (xe:xes)            = xe:(outerScTr xes)

mkOuterScTr x bs ((NonRec y (Case (Var z) b ys ec)):xes) | z == x
  = mkOuterScTr x ((NonRec y (Case (Var z) b ys ec)):bs) xes
mkOuterScTr x bs xes = (bs++(outerScTr xes))

innerScTr = mapBnd scTrans

scTrans x e = mapExpr scTrans $ foldr Let e0 bs
  where (bs, e0) = collectBnds x [] e 

collectBnds x bs (Let b@(NonRec y (Case (Var v) _  _ _ )) e) | x == v
  = collectBnds x (b:bs) e
collectBnds x bs (Tick t e) = collectBnds x bs e
collectBnds _ bs e          = (bs, e)


type TE = State TrEnv

data TrEnv = Tr { freshIndex  :: !Int
                , loc         :: SrcSpan
                }

initEnv = Tr 0 noSrcSpan

transPg cbs = mapM transBd cbs

transBd (NonRec x e) = transExpr e >>= return . NonRec x
transBd b            = return b

transExpr :: CoreExpr -> TE CoreExpr
transExpr e
  | chkRec e1'
  = trans tvs ids bs e1' >>= return . keepLam e 
  | otherwise
  = return e
  where (tvs, ids, e') = collectTyAndValBinders e
        (bs, e1')      = collectNonRecLets e'
        e2'            = e

collectNonRecLets e = go [] e
  where go bs (Let b@(NonRec _ _) e') = go (b:bs) e'
        go bs e                       = (reverse bs, e)

keepLam (Lam x e') e = Lam x (keepLam e' e)
keepLam e1 e2        = e2

appTysAndIds tvs ids x = mkApps (mkTyApps (Var x) (map TyVarTy tvs)) (map Var ids)

trXEs :: [TyVar] -> [Id]-> (CoreBndr, CoreExpr) -> TE (CoreBndr, CoreExpr, [Id])
trXEs vs ids (x, e) 
  = do ids'    <- mapM fresh ids
       let t   = subTy sTy $ mkForAllTys vs' $ mkType (reverse ids') $ varType x
       let x'  = setVarType x t
       let s   = M.fromList $ zip ids (map Var ids') 
       return 	(x', appTysAndIds vs ids' x', ids')
   where vs'  = vs 
         tvs' = map TyVarTy vs'
         sTy  = M.fromList $ zip vs tvs'

-- trans :: [TyVar] -> [Id] -> CoreExpr -> TE  CoreExpr
trans vs ids [] (Let (Rec xes) e)
 = do fids <- mapM (mkFreshIds vs ids) xs
      let (ftvs, fxids, fxs) = unzip3 fids
      (se, rs) <- mkFreshBdrs vs ids xs fxs
      let mkSu tvs ids0 = mkSubs ids tvs ids0 (zip xs fxs)
      let mkE tvs ids0 e = mkCoreLams (tvs ++ ids0) (sub (mkSu tvs ids0) e)
      let es' = zipWith3 mkE ftvs fxids es
      let xes' = zip fxs es'
      return $ Let (Rec (xes' ++ rs)) (sub se e)
 where (xs, es) = unzip xes

trans vs ids bs (Let (Rec xes) e)
 = trans vs ids [] (Let (Rec (zip xs es')) e)
 where (xs, es) = unzip xes
       es'      = map (\e0 -> foldr Let e0 bs) es

mkSubs ids tvs ids0 xxs'   
  = M.fromList $ s1 ++ s2
  where s1 = map (mkSub ids tvs ids0) xxs'
        s2 = zip ids (map Var ids0)

mkSub ids tvs ids0 (x, x') = (x, appTysAndIds tvs ids0 x')	

mkFreshBdrs tvs ids xs xs'
  = do xs0'     <- mapM fresh xs
       let xxs  = zip xs (map Var xs0')
       let s    = M.fromList xxs
       let ls   = zipWith (\x0' x' -> (x0', appTysAndIds tvs ids x')) xs0' xs'
       return (s, ls)

mkFreshIds tvs ids x
  = do ids'     <- mapM fresh ids
       let tvs' =  tvs
       let t    = mkForAllTys tvs' $ mkType (reverse ids') $ varType x
       let x'   = setVarType x t
       return (tvs', ids', x')

mkType [] t = t
mkType (id:ids) t = mkType ids $ FunTy (varType id) t

chkRec (Let (Rec xes) e) = True
chkRec _                 = False

instance Show (Expr Var) where 
 show = showSDoc . ppr

instance Show (Bag Message) where
  show = showSDoc . pprMessageBag

instance Show (Bind CoreBndr) where
  show = showSDoc . ppr


class Freshable a where
 fresh :: a -> TE a

instance Freshable Int where
  fresh _ = freshInt

instance Freshable Unique where
  fresh _ = freshUnique

instance Freshable Var where
  fresh v = liftM (setVarUnique v) freshUnique

freshInt
  = do s <- get
       let n = freshIndex s
       put s{freshIndex = n+1}
       return n

freshUnique = freshInt >>= return . mkUnique 'X'

class Subable a where
  sub   :: (M.Map CoreBndr CoreExpr) -> a -> a
  subTy :: (M.Map TyVar Type) -> a -> a

instance Subable CoreExpr where
 sub s (Var v)        = M.findWithDefault (Var v) v s
 sub s (Lit l)        = Lit l
 sub s (App e1 e2)    = App (sub s e1) (sub s e2)
 sub s (Lam b e)      = Lam b (sub s e)
 sub s (Let b e)      = Let (sub s b) (sub s e)
 sub s (Case e b t a) = Case (sub s e) (sub s b) t (map (sub s) a)
 sub s (Cast e c)     = Cast (sub s e) c
 sub s (Tick t e)     = Tick t (sub s e)
 sub s (Type t)       = Type t
 sub s (Coercion c)   = Coercion c

 subTy s (Var v) = Var (subTy s v)
 subTy s (Lit l) = Lit l
 subTy s (App e1 e2) = App (subTy s e1) (subTy s e2)
 subTy s (Lam b e)   | isTyVar b
	 = Lam v' (subTy s e)
  where v' = case (M.lookup b s) of 
              Nothing           -> b
              Just (TyVarTy v') -> v'
 subTy s (Lam b e)   = Lam (subTy s b) (subTy s e)
 subTy s (Let b e)   = Let (subTy s b) (subTy s e)
 subTy s (Case e b t a) = Case (subTy s e) (subTy s b) (subTy s t) (map (subTy s) a)
 subTy s (Cast e c)     = Cast (subTy s e) (subTy s c)
 subTy s (Tick t e)     = Tick t (subTy s e)
 subTy s (Type t) = Type (subTy s t)
 subTy s (Coercion c) = Coercion (subTy s c)

instance Subable Coercion where
 sub s c   = c
 subTy s c = error "subTy Coercion"

instance Subable (Alt Var) where 
 sub s (a, b, e)   = (a, (map (sub s) b), sub s e)
 subTy s (a, b, e) = (a, (map (subTy s) b), subTy s e)

instance Subable Var where
 sub s v   = if (M.member v s) then error "sub Var" else v
 subTy s v = setVarType v (subTy s (varType v))
								
instance Subable (Bind Var) where
 sub s (NonRec x e)   = NonRec (sub s x) (sub s e)
 sub s (Rec xes)      = Rec (map (\(x, e) -> (sub s x, sub s e)) xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec (map (\(x, e) -> (subTy s x, subTy s e)) xes)

instance Subable Type where
 sub s e   = e
 subTy     = substTysWith	

substTysWith s tv@(TyVarTy v)  = M.findWithDefault tv v s
substTysWith s (FunTy t1 t2)   = FunTy (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t)  = ForAllTy v (substTysWith (M.delete v s) t)
substTysWith s (TyConApp c ts) = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)   = AppTy (substTysWith s t1) (substTysWith s t2)

mapBnd f (NonRec b e) = NonRec b (mapExpr f  e)
mapBnd f (Rec bs)     = Rec (map (\(x, e) -> (x, mapExpr f e)) bs)

mapExpr f (Let b@(NonRec x ex) e) = Let b (f x e)
mapExpr f (App e1 e2)             = App  (mapExpr f e1) (mapExpr f e2)
mapExpr f (Lam b e)               = Lam b (mapExpr f e)
mapExpr f (Let bs e)              = Let (mapBnd f bs) (mapExpr f e)
mapExpr f (Case e b t alt)        = Case e b t (map (mapAlt f) alt)
mapExpr f (Tick t e)              = Tick t (mapExpr f e)
mapExpr _  e                      = e

mapAlt f (d, bs, e) = (d, bs, mapExpr f e)
