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
transformRecExpr x 
  = if (isEmptyBag e) then pg else error ("Type-check" ++ show e)
  where pg = map trBind x
        (w, e) = lintCoreBindings pg

type TE = State TrEnv

data TrEnv = Tr { freshIndex  :: !Int
                , loc         :: SrcLoc
                }

trBind (NonRec x e) = trace ("trBind" ++ showSDoc (ppr x) ++ bar (varType x)) $ NonRec x $ e'
  where e' = trE e
trBind b            = b

bar (ForAllTy v t) = "ForAllTy" ++ show v ++ bar t
bar (AppTy t1 t2)  = "AppTy" ++ bar t1 ++ bar t2
bar (FunTy t1 t2)  = "FunTy" ++ bar t1 ++ bar t2
bar (TyVarTy v)    = "Var" ++ show v
bar (TyConApp c ts)  = "TyConApp " ++ showSDoc (ppr c) ++ concatMap (showSDoc . ppr) ts

printTy (Var v) = "Var " ++ show v ++ " : " ++ showPpr (varType v)
printTy e@(App e1 e2) = "App " ++showPpr(exprType e)++ "\n of " ++ printTy e1 ++"\nand\n" ++ printTy e2
printTy (Lam b e) = "Lam " ++ show b ++ show e
printTy _         = ""
trE :: CoreExpr -> CoreExpr
trE e = if chkRec e' then {-subTy s-} (foo e e2') else e
  where (tvs, ids, e') = collectTyAndValBinders e
        s = M.fromList $ zip tvs (map TyVarTy tvs')
        e1 = subTy s e
        e2 = subTy s (tr2 tvs ids e')
        e2' = (tr2 tvs ids e')
        tvs' = map (\(a, n) -> freshTyVar (50000+n) 'Y' a) (zip tvs [1..])
        ids' = map (subTy s) ids
foo (Lam x e') e = Lam x (foo e' e)
foo e1 e2        = e2

tr2 :: [TyVar] -> [Id] -> CoreExpr -> CoreExpr -- , M.Map CoreBndr CoreExpr)
tr2 vs ids (Let (Rec xes) e) 
--  = (Let (Rec (xes' ++ zip ids' es' ) ) (sub m e))
  = (Let (Rec (xes')) (sub m e))
  where (xs, es) = unzip xes
--         m = M.fromList ls -- $ zip xs $ trace (concatMap printTy es') es'
        m = M.fromList $ zip xs es'
        (xs', es', es'') = unzip3 (map (trV vs ids) xes)
        xes' = zip xs' (map (sub m) es'')
--         ls = zip xs (map Var ids')
--         ids' = map (\(id, n) -> freshId n id ) $ zip xs [1..]
trV :: [TyVar] -> [Id]-> (CoreBndr, CoreExpr) -> (CoreBndr, CoreExpr, CoreExpr)
trV vs ids (x, e) = (x',  mkApps (mkTyApps (Var x') tvs)(map Var ids'),  mkCoreLams (vs' ++ ids') (sub s {-(subTy sTy-} e))
   where t   = subTy sTy $ mkForAllTys vs' $ mkType (reverse ids') $ varType x
         vs' = vs -- map (\(a, n) -> freshTyVar (400+n) 'W' a) (zip vs [1..])
         x'  = traceShow ("type of " ++ show x ++ showSDoc (ppr t)) $setVarType x t
         tvs = map TyVarTy vs
         tvs' = map TyVarTy vs'
         sTy  = M.fromList $ zip vs tvs'
--         ids' = map (\(id, n) -> freshId (90+n) 'X' id (varType id)) $ zip ids [1..] 
         ids' = ids -- map (\(id, n) -> freshId (90+n) 'R' id (subTy sTy (varType id))) $ zip ids [1..] 
         s = M.fromList $ zip ids (map Var ids') 

mkType [] t = t
mkType (id:ids) t = mkType ids $ FunTy (varType id) t

chkRec (Let (Rec xes) e) = True
chkRec _                 = False

freshId nu id = setVarUnique id u
-- freshId nu c id t = setVarName (setVarUnique id u) nm
--freshId nu c id t = setVarName (setVarUnique (setVarType id t) u) nm
  where u = deriveUnique (varUnique id) nu 'X'
        n = mkVarOcc "δ"
        nm = mkInternalName u n noSrcSpan

freshTyVar nu c a = setVarUnique (setVarName a nm) u
  where u = deriveUnique  (varUnique a) nu c
        n = mkVarOcc ("β" ++ show nu )
        nm = mkInternalName u n noSrcSpan

deriveUnique _ delta c = mkUnique 'X' (100 + delta)

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
 sub s (Var v) = M.findWithDefault (Var v) v s
 sub s (Lit l) = Lit l
 sub s (App e1 e2) = App (sub s e1) (sub s e2)
 sub s (Lam b e)   = Lam b (sub s e)
 sub s (Let b e)   = Let (sub s b) (sub s e)
 sub s (Case e b t a) = Case (sub s e) (sub s b) t (map (sub s) a)
 sub s (Cast e c)     = Cast (sub s e) c
 sub s (Tick t e)            = Tick t (sub s e)
 sub s (Type t) = Type t
 sub s (Coercion c) = Coercion c

 subTy s (Var v) = Var (subTy s v)
 subTy s (Lit l) = Lit l
 subTy s (App e1 e2) = App (subTy s e1) (subTy s e2)
 subTy s (Lam b e)   | isTyVar b
	 = Lam v' (subTy s e)
  where v' = case (M.lookup b s) of 
              Nothing -> b
              Just (TyVarTy v') -> v'
 subTy s (Lam b e)   = Lam (subTy s b) (subTy s e)
 subTy s (Let b e)   = Let (subTy s b) (subTy s e)
 subTy s (Case e b t a) = Case (subTy s e) (subTy s b) (subTy s t) (map (subTy s) a)
 subTy s (Cast e c)     = Cast (subTy s e) (subTy s c)
 subTy s (Tick t e)     = Tick t (subTy s e)
 subTy s (Type t) = Type (subTy s t)
 subTy s (Coercion c) = Coercion (subTy s c)

instance Subable Coercion where
 sub s c = c
 subTy s c = error "subTy Coercion"

instance Subable (Alt Var) where 
 sub s (a, b, e) = (a, (map (sub s) b), sub s e)
 subTy s (a, b, e) = (a, (map (subTy s) b), subTy s e)

instance Subable Var where
 sub s v   = if (M.member v s) then error "sub Var" else v
 subTy s v =  setVarType v (subTy s (varType v))
								
instance Subable (Bind Var) where
 sub s (NonRec x e) = NonRec (sub s x) (sub s e)
 sub s (Rec xes)    = Rec (map (\(x, e) -> (sub s x, sub s e)) xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec (map (\(x, e) -> (subTy s x, subTy s e)) xes)

instance Subable Type where
 sub s e   = e
 subTy = substTysWith	

substTysWith s tv@(TyVarTy v) = M.findWithDefault tv v s
substTysWith s (FunTy t1 t2)  = FunTy (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t) = ForAllTy v' (substTysWith s t)
   where v' = case (M.lookup v s) of  
               Nothing    -> v
               Just (TyVarTy a) -> a
-- substTysWith s (ForAllTy v t) = ForAllTy v (substTysWith s t)
substTysWith s (TyConApp c ts) = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)  = AppTy (substTysWith s t1) (substTysWith s t2)


