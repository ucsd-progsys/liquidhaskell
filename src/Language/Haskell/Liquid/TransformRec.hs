{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Language.Haskell.Liquid.TransformRec (
     transformRecExpr, transformScope
     ) where

import           Bag
import           Coercion
import           Control.Arrow       (second, (***))
import           Control.Monad.State
import           CoreLint
import           CoreSyn
import qualified Data.HashMap.Strict as M
import           ErrUtils
import           Id                  (idOccInfo, setIdInfo)
import           IdInfo
import           MkCore              (mkCoreLams)
import           SrcLoc
import           Type                (mkForAllTys)
import           TypeRep
import           Unique              hiding (deriveUnique)
import           Var
import           Language.Haskell.Liquid.GhcMisc
import           Language.Haskell.Liquid.Misc (mapSndM)

import           Data.List                (foldl', isInfixOf)
import           Control.Applicative      ((<$>))

transformRecExpr :: CoreProgram -> CoreProgram
transformRecExpr cbs
  | isEmptyBag $ filterBag isTypeError e
  =  {-trace "new cbs"-} pg 
  | otherwise 
  = error (showPpr pg ++ "Type-check" ++ showSDoc (pprMessageBag e))
  where pg     = evalState (transPg cbs) initEnv
        (_, e) = lintCoreBindings pg

isTypeError s | isInfixOf "Non term variable" (showSDoc s) = False
isTypeError _ = True

scopeTr = outerScTr . innerScTr
transformScope = outerScTr . innerScTr

outerScTr = mapNonRec (go [])
  where
   go ack x (xe : xes) | isCaseArg x xe = go (xe:ack) x xes
   go ack _ xes        = ack ++ xes

isCaseArg x (NonRec _ (Case (Var z) _ _ _)) = z == x
isCaseArg _ _                               = False

innerScTr = (mapBnd scTrans <$>)

scTrans x e = mapExpr scTrans $ foldr Let e0 bs
  where (bs, e0)           = go [] x e
        go bs x (Let b e)  | isCaseArg x b = go (b:bs) x e
        go bs x (Tick t e) = second (Tick t) $ go bs x e
        go bs x e          = (bs, e)

type TE = State TrEnv

data TrEnv = Tr { freshIndex  :: !Int
                , loc         :: SrcSpan
                }

initEnv = Tr 0 noSrcSpan

transPg = mapM transBd

transBd (NonRec x e) = liftM (NonRec x) (transExpr =<< mapBdM transBd e)
transBd (Rec xes)    = liftM Rec $ mapM (mapSndM (mapBdM transBd)) xes

transExpr :: CoreExpr -> TE CoreExpr
transExpr e
  | (isNonPolyRec e') && (not (null tvs)) 
  = trans tvs ids bs e'
  | otherwise
  = return e
  where (tvs, ids, e'')       = collectTyAndValBinders e
        (bs, e')              = collectNonRecLets e''

isNonPolyRec (Let (Rec xes) _) = any nonPoly (snd <$> xes)
isNonPolyRec _                 = False

nonPoly = null . fst . collectTyBinders

collectNonRecLets = go []
  where go bs (Let b@(NonRec _ _) e') = go (b:bs) e'
        go bs e'                      = (reverse bs, e')

appTysAndIds tvs ids x = mkApps (mkTyApps (Var x) (map TyVarTy tvs)) (map Var ids)

trans vs ids bs (Let (Rec xes) e)
  = liftM (mkLam . mkLet) (makeTrans vs liveIds e')
  where liveIds = mkAlive <$> ids
        mkLet e = foldr Let e bs
        mkLam e = foldr Lam e $ vs ++ liveIds
        e'      = Let (Rec xes') e
        xes'    = (second mkLet) <$> xes

makeTrans vs ids (Let (Rec xes) e)
 = do fids    <- mapM (mkFreshIds vs ids) xs
      let (ids', ys) = unzip fids
      let yes  = appTysAndIds vs ids <$> ys
      ys'     <- mapM fresh xs
      let su   = M.fromList $ zip xs (Var <$> ys')
      let rs   = zip ys' yes
      let es'  = zipWith (mkE ys) ids' es
      let xes' = zip ys es'
      return   $ mkRecBinds rs (Rec xes') (sub su e)
 where 
   (xs, es)       = unzip xes
   mkSu ys ids'   = mkSubs ids vs ids' (zip xs ys)
   mkE ys ids' e' = mkCoreLams (vs ++ ids') (sub (mkSu ys ids') e')

mkRecBinds :: [(b, Expr b)] -> Bind b -> Expr b -> Expr b
mkRecBinds xes rs e = Let rs (foldl' f e xes)
  where f e (x, xe) = Let (NonRec x xe) e  

mkSubs ids tvs xs ys = M.fromList $ s1 ++ s2
  where s1 = (second (appTysAndIds tvs xs)) <$> ys
        s2 = zip ids (Var <$> xs)

mkFreshIds tvs ids x
  = do ids'  <- mapM fresh ids
       let t  = mkForAllTys tvs $ mkType (reverse ids') $ varType x
       let x' = setVarType x t
       return (ids', x')
  where 
    mkType ids ty = foldl (\t x -> FunTy (varType x) t) ty ids

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

freshUnique = liftM (mkUnique 'X') freshInt

mkAlive x
  | isId x && isDeadOcc (idOccInfo x)
  = setIdInfo x (setOccInfo (idInfo x) NoOccInfo)
  | otherwise
  = x

class Subable a where
 sub   :: M.HashMap CoreBndr CoreExpr -> a -> a
 subTy :: M.HashMap TyVar Type -> a -> a

instance Subable CoreExpr where
  sub s (Var v)        = M.lookupDefault (Var v) v s
  sub _ (Lit l)        = Lit l
  sub s (App e1 e2)    = App (sub s e1) (sub s e2)
  sub s (Lam b e)      = Lam b (sub s e)
  sub s (Let b e)      = Let (sub s b) (sub s e)
  sub s (Case e b t a) = Case (sub s e) (sub s b) t (map (sub s) a)
  sub s (Cast e c)     = Cast (sub s e) c
  sub s (Tick t e)     = Tick t (sub s e)
  sub _ (Type t)       = Type t
  sub _ (Coercion c)   = Coercion c

  subTy s (Var v)      = Var (subTy s v)
  subTy _ (Lit l)      = Lit l
  subTy s (App e1 e2)  = App (subTy s e1) (subTy s e2)
  subTy s (Lam b e)    | isTyVar b = Lam v' (subTy s e)
   where v' = case M.lookup b s of
               Nothing          -> b
               Just (TyVarTy v) -> v

  subTy s (Lam b e)      = Lam (subTy s b) (subTy s e)
  subTy s (Let b e)      = Let (subTy s b) (subTy s e)
  subTy s (Case e b t a) = Case (subTy s e) (subTy s b) (subTy s t) (map (subTy s) a)
  subTy s (Cast e c)     = Cast (subTy s e) (subTy s c)
  subTy s (Tick t e)     = Tick t (subTy s e)
  subTy s (Type t)       = Type (subTy s t)
  subTy s (Coercion c)   = Coercion (subTy s c)

instance Subable Coercion where
  sub _ c                = c
  subTy _ _              = error "subTy Coercion"

instance Subable (Alt Var) where
 sub s (a, b, e)   = (a, map (sub s) b,   sub s e)
 subTy s (a, b, e) = (a, map (subTy s) b, subTy s e)

instance Subable Var where
 sub s v   | M.member v s = subVar $ s M.! v 
           | otherwise    = v
 subTy s v = setVarType v (subTy s (varType v))

subVar (Var x) = x
subVar  _      = error "sub Var"

instance Subable (Bind Var) where
 sub s (NonRec x e)   = NonRec (sub s x) (sub s e)
 sub s (Rec xes)      = Rec ((sub s *** sub s) <$> xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec ((subTy s  *** subTy s) <$> xes)

instance Subable Type where
 sub _ e   = e
 subTy     = substTysWith

substTysWith s tv@(TyVarTy v)  = M.lookupDefault tv v s
substTysWith s (FunTy t1 t2)   = FunTy (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t)  = ForAllTy v (substTysWith (M.delete v s) t)
substTysWith s (TyConApp c ts) = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)   = AppTy (substTysWith s t1) (substTysWith s t2)

mapNonRec f (NonRec x xe:xes) = NonRec x xe : f x (mapNonRec f xes)
mapNonRec f (xe:xes)          = xe : mapNonRec f xes
mapNonRec _ []                = []

mapBnd f (NonRec b e)             = NonRec b (mapExpr f  e)
mapBnd f (Rec bs)                 = Rec (map (second (mapExpr f)) bs)

mapExpr f (Let (NonRec x ex) e)   = Let (NonRec x (f x ex) ) (f x e)
mapExpr f (App e1 e2)             = App  (mapExpr f e1) (mapExpr f e2)
mapExpr f (Lam b e)               = Lam b (mapExpr f e)
mapExpr f (Let bs e)              = Let (mapBnd f bs) (mapExpr f e)
mapExpr f (Case e b t alt)        = Case e b t (map (mapAlt f) alt)
mapExpr f (Tick t e)              = Tick t (mapExpr f e)
mapExpr _  e                      = e

mapAlt f (d, bs, e) = (d, bs, mapExpr f e)

-- Do not apply transformations to inner code

mapBdM _ = return

-- mapBdM f (Let b e)        = liftM2 Let (f b) (mapBdM f e)
-- mapBdM f (App e1 e2)      = liftM2 App (mapBdM f e1) (mapBdM f e2)
-- mapBdM f (Lam b e)        = liftM (Lam b) (mapBdM f e)
-- mapBdM f (Case e b t alt) = liftM (Case e b t) (mapM (mapBdAltM f) alt)
-- mapBdM f (Tick t e)       = liftM (Tick t) (mapBdM f e)
-- mapBdM _  e               = return  e
-- 
-- mapBdAltM f (d, bs, e) = liftM ((,,) d bs) (mapBdM f e)
