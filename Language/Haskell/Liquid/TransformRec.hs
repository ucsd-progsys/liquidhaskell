{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Language.Haskell.Liquid.TransformRec (
     transformRecExpr
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
import           Outputable
import           SrcLoc
import           Type                (mkForAllTys)
import           TypeRep
import           Unique              hiding (deriveUnique)
import           Var
import           Language.Haskell.Liquid.GhcMisc

transformRecExpr :: CoreProgram -> CoreProgram
transformRecExpr cbs
  | isEmptyBag e
  =  {-trace "new cbs"-} pg 
  | otherwise 
  = error (showPpr pg ++ "Type-check" ++ showSDoc (pprMessageBag e))
  where pg     = scopeTr $ evalState (transPg cbs) initEnv
        (_, e) = lintCoreBindings pg

scopeTr = outerScTr . map innerScTr

outerScTr []                  = []
outerScTr (NonRec x ex : xes) = NonRec x ex : mkOuterScTr x [] xes
outerScTr (xe:xes)            = xe : outerScTr xes

mkOuterScTr x bs (NonRec y (Case (Var z) b ys ec) : xes) | z == x
  = mkOuterScTr x (NonRec y (Case (Var z) b ys ec) : bs) xes
mkOuterScTr _ bs xes
  = bs ++ outerScTr xes

innerScTr = mapBnd scTrans

scTrans x e = mapExpr scTrans $ foldr Let e0 bs
  where (bs, e0) = collectBnds x [] e

collectBnds ::  Id -> [Bind t] -> Expr t -> ([Bind t], Expr t)
collectBnds x bs (Let b@(NonRec _ (Case (Var v) _  _ _ )) e)
  | x == v
  = collectBnds x (b:bs) e
collectBnds x bs (Tick t e)
  = (bs', Tick t e')
    where (bs', e') = collectBnds x bs e
collectBnds _ bs e
  = (bs, e)


type TE = State TrEnv

data TrEnv = Tr { freshIndex  :: !Int
                , loc         :: SrcSpan
                }

initEnv = Tr 0 noSrcSpan

transPg = mapM transBd

applyTransToAllBds = False

transBd (NonRec x e)
  | applyTransToAllBds
  = liftM (NonRec x) (transExpr =<< (mapBdM transBd e))
  | otherwise
  = liftM (NonRec x) (transExpr e)
transBd e@(Rec xes)
  | applyTransToAllBds
  = liftM Rec (mapM (\(x, e) -> liftM ((,) x) (mapBdM transBd e)) xes)
  | otherwise
  = return e

transExpr :: CoreExpr -> TE CoreExpr
transExpr e
  | chkRec e1'
  = trans tvs ids bs e1'
  | otherwise
  = return e
  where (tvs, ids, e') = collectTyAndValBinders e
        (bs, e1')      = collectNonRecLets e'
        -- e2'            = e

collectNonRecLets = go []
  where go bs (Let b@(NonRec _ _) e') = go (b:bs) e'
        go bs e'                      = (reverse bs, e')

appTysAndIds tvs ids x = mkApps (mkTyApps (Var x) (map TyVarTy tvs)) (map Var ids)

--trXEs :: [TyVar] -> [Id]-> (CoreBndr, CoreExpr) -> TE (CoreBndr, CoreExpr, [Id])
--trXEs vs ids (x, e)
--  = do ids'    <- mapM fresh ids
--       let t   = subTy sTy $ mkForAllTys vs' $ mkType (reverse ids') $ varType x
--       let x'  = setVarType x t
--       let s   = M.fromList $ zip ids (map Var ids')
--       return   (x', appTysAndIds vs ids' x', ids')
--   where vs'  = vs
--         tvs' = map TyVarTy vs'
--         sTy  = M.fromList $ zip vs tvs'

trans vs ids bs e
  = liftM mkLet (trans_ vs liveIds bs e)
  where liveIds = map mkAlive ids
        -- e' = sub (M.fromList (zip ids (map Var liveIds))) e
        mkLet es = foldr Lam es (vs ++ liveIds)

trans_ vs ids [] (Let (Rec xes) e)
 = do fids <- mapM (mkFreshIds vs ids) xs
      let (ftvs, fxids, fxs) = unzip3 fids
      (se, rs) <- mkFreshBdrs vs ids xs fxs
      let mkSu tvs ids0   = mkSubs ids tvs ids0 (zip xs fxs)
      let mkE tvs ids0 e' = mkCoreLams (tvs ++ ids0) (sub (mkSu tvs ids0) e')
      let es' = zipWith3 mkE ftvs fxids es
      let xes' = zip fxs es'
      return $ Let (Rec (xes' ++ rs)) (sub se e)
 where (xs, es) = unzip xes

trans_ vs ids bs (Let (Rec xes) e)
 = liftM mkLet $ trans_ vs ids [] (Let (Rec (zip xs es')) e)
 where (xs, es) = unzip xes
       es'      = map (\e0 -> foldr Let e0 bs) es
       mkLet e' = foldr Let e' bs

mkSubs ids tvs ids0 xxs'
  = M.fromList $ s1 ++ s2
  where s1 = map (mkSub ids tvs ids0) xxs'
        s2 = zip ids (map Var ids0)

mkSub _ tvs ids0 (x, x') = (x, appTysAndIds tvs ids0 x')

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

-- Hlint!
mkType ids ty = foldl (\t x -> FunTy (varType x) t) ty ids
-- mkType [] t = t
-- mkType (id:ids) t = mkType ids $ FunTy (varType id) t


chkRec (Let (Rec _) _) = True
chkRec _               = False

--instance Show (Expr Var) where
-- show = showSDoc . ppr
--
--instance Show (Bag Message) where
--  show = showSDoc . pprMessageBag
--
--instance Show (Bind CoreBndr) where
--  show = showSDoc . ppr

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

-- freshUnique = freshInt >>= return . mkUnique 'X'
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

  subTy s (Var v) = Var (subTy s v)
  subTy _ (Lit l) = Lit l
  subTy s (App e1 e2) = App (subTy s e1) (subTy s e2)
  subTy s (Lam b e)   | isTyVar b
      = Lam v' (subTy s e)
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
 sub s v   = if M.member v s then subVar $ s M.! v else v
   where subVar (Var x) = x
         subVar  _      = error "sub Var"
 subTy s v = setVarType v (subTy s (varType v))

instance Subable (Bind Var) where
 sub s (NonRec x e)   = NonRec (sub s x) (sub s e)
 sub s (Rec xes)      = Rec (map (sub s *** sub s) xes)
-- sub s (Rec xes)      = Rec (map (\(x, e) -> (sub s x, sub s e)) xes)

 subTy s (NonRec x e) = NonRec (subTy s x) (subTy s e)
 subTy s (Rec xes)    = Rec (map (subTy s  *** subTy s) xes)
 -- subTy s (Rec xes)    = Rec (map (sub s  *** sub s) (\(x, e) -> (subTy s x, subTy s e)) xes)


instance Subable Type where
 sub _ e   = e
 subTy     = substTysWith

substTysWith s tv@(TyVarTy v)  = M.lookupDefault tv v s
substTysWith s (FunTy t1 t2)   = FunTy (substTysWith s t1) (substTysWith s t2)
substTysWith s (ForAllTy v t)  = ForAllTy v (substTysWith (M.delete v s) t)
substTysWith s (TyConApp c ts) = TyConApp c (map (substTysWith s) ts)
substTysWith s (AppTy t1 t2)   = AppTy (substTysWith s t1) (substTysWith s t2)

mapBnd f (NonRec b e)             = NonRec b (mapExpr f  e)
mapBnd f (Rec bs)                 = Rec (map (second (mapExpr f)) bs)
-- mapBnd f (Rec bs)     = Rec (map (\(x, e) -> (x, mapExpr f e)) bs)

mapExpr f (Let b@(NonRec x _) e)  = Let b (f x e)
mapExpr f (App e1 e2)             = App  (mapExpr f e1) (mapExpr f e2)
mapExpr f (Lam b e)               = Lam b (mapExpr f e)
mapExpr f (Let bs e)              = Let (mapBnd f bs) (mapExpr f e)
mapExpr f (Case e b t alt)        = Case e b t (map (mapAlt f) alt)
mapExpr f (Tick t e)              = Tick t (mapExpr f e)
mapExpr _  e                      = e

mapAlt f (d, bs, e) = (d, bs, mapExpr f e)

mapBdM f (Let b e)        = liftM2 Let (f b) (mapBdM f e)
mapBdM f (App e1 e2)      = liftM2 App (mapBdM f e1) (mapBdM f e2)
mapBdM f (Lam b e)        = liftM (Lam b) (mapBdM f e)
mapBdM f (Case e b t alt) = liftM (Case e b t) (mapM (mapBdAltM f) alt)
mapBdM f (Tick t e)       = liftM (Tick t) (mapBdM f e)
mapBdM _  e               = return  e

mapBdAltM f (d, bs, e) = liftM ((,,) d bs) (mapBdM f e)
