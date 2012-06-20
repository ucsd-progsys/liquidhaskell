{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}
module Language.Haskell.Liquid.Predicates (
    predType
  , generatePredicates
  ) where

import Type
import Var
import OccName (mkTyVarOcc)
import Name (mkInternalName)
import Unique (initTyVarUnique)
import TypeRep
import Var
import TyCon
import SrcLoc
import CoreSyn
import CoreUtils
import qualified DataCon as TC
import Outputable hiding (empty)
import IdInfo
import TysWiredIn

import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.PredType
import Language.Haskell.Liquid.GhcMisc (stringTyVar, tickSrcSpan)
import Language.Haskell.Liquid.RefType 
import Language.Haskell.Liquid.Misc
import qualified Language.Haskell.Liquid.Fixpoint as F

import Control.Monad.State
import Control.Applicative      ((<$>))
import qualified Data.Map as M
import qualified Data.List as L
import Data.List (foldl')
import Control.DeepSeq
import Data.Data hiding (TyCon)

predType :: Type
predType = TyVarTy $ stringTyVar "Pred"

----------------------------------------------------------------------
---- Predicate Environments ------------------------------------------
----------------------------------------------------------------------

consAct info = foldM consCB (initEnv info) $ cbs info

generatePredicates ::  GhcInfo -> ([CoreSyn.Bind CoreBndr], F.SEnv PrType)
generatePredicates info = {-trace ("Predicates\n" ++ show γ ++ "PredCBS" ++ show cbs')-} (cbs', nPd)
  where γ    = fmap removeExtPreds (penv $ evalState act (initPI info))
        act  = consAct info
        cbs' = addPredApp nPd <$> cbs info
--         γ'   = filterGamma nPd γ 
        nPd  = getNeedPd info

instance Show CoreBind where
  show = showSDoc . ppr

γ += (x, t) = γ { penv = F.insertSEnv x t (penv γ)}
γ ??= x = F.lookupSEnv x γ


γ ?= x 
  = case (F.lookupSEnv x (penv γ)) of 
      Just t  -> refreshTy t
      Nothing -> error $ "SEnvlookupR: unknown = " ++ showPpr x

data PCGEnv 
  = PCGE { loc  :: !SrcSpan
         , penv :: !(F.SEnv PrType)
         }

data PInfo 
  = PInfo { freshIndex :: !Integer
          , pMap       :: !(M.Map (PVar Type) (Predicate Type))
          , hsCsP      :: ![SubC]
          , tyCons     :: !(M.Map TyCon TyConP)
          , symbolsP   :: !(M.Map F.Symbol F.Symbol)
          }

data SubC    
  = SubC { senv :: !PCGEnv
         , lhs  :: !PrType
         , rhs  :: !PrType
         }

addId x y = modify $ \s -> s{symbolsP = M.insert x y (symbolsP s)}

initPI info = PInfo { freshIndex = 1
                    , pMap = M.empty
                    , hsCsP = []
                    , tyCons = M.fromList (tconsP info)
                    , symbolsP = M.empty
                    }

type PI = State PInfo

consCB' γ (NonRec x e)
  = do t <- consE γ e
--       tg <- generalizeS t
       return $ γ += (mkSymbol x, t)

consCB' γ (Rec xes) 
  = do ts       <- mapM (\e -> freshTy $ exprType e) es
--       let tsga = generalizeArgs <$> ts
       let γ'   = foldl' (+=) γ (zip vs ts)
       zipWithM_ (cconsE γ') es ts
--       tsg   <- forM ts generalizeS
       return $ foldl' (+=) γ (zip vs ts)
    where (xs, es) = unzip xes
          vs       = mkSymbol <$> xs

checkOneToOne :: [(Predicate Type, Predicate Type)] -> Bool
checkOneToOne xys = and [y1 == y2 | (x1, y1) <- xys, (x2, y2) <- xys, x1 == x2]

tyCheck x Nothing t2
  = False 
tyCheck x (Just t1) t2
  = if b then (checkOneToOne (rmTs ps)) else (error "msg") 
  where (b, (ps, msg)) =  runState (tyC t1 t2) ([], "tyError in " ++ show x ++ show t1 ++ show t2)
        
rmTs = filter rmT        
  where rmT (_, Pr []) = False
        rmT (Pr [], _) = error "tmTs in tyC"
        rmT (_    , _) = True

--rmTs ((_     , PdTrue):ls) = rmTs ls
--rmTs ((PdTrue, _     ):ls) = error "tmTs in tyC"
--rmTs ((p1    , p2    ):ls) = (p1, p2): (rmTs ls)
--rmTs [] = []


tyC (RAll (RP _) t1) t2 
  = tyC t1 t2

tyC t1 (RAll (RP _) t2) 
  = tyC t1 t2

tyC (RAll (RV v1) t1) (RAll (RV v2) t2) 
  = tyC (subsTyVars (v1, RVar (RV v2) pdTrue) t1) t2

tyC (RVar (RV v1) p1) (RVar (RV v2) p2)
  = do modify $ \(ps, msg) -> ((p2, p1):ps, msg)
       return $ v1 == v2

tyC (RApp c1 ts1 ps1 p1) (RApp c2 ts2 ps2 p2)
  = do modify $ \(ps, msg) -> ((p2, p1):(ps ++ zip ps2 ps1), msg)
       b <- zipWithM tyC ts1 ts2
       return $ and b && c1 == c2

tyC (RCls c1 _) (RCls c2 _) 
  = return $ c1 == c2

tyC (RFun (RB x) t1 t2) (RFun (RB x') t1' t2')
  = do b1 <- tyC t1 t1'
       b2 <- tyC (substSym (x, x') t2) t2'
       return $ b1 && b2

tyC t1 t2 
  = error $ "\n " ++ show t1 ++ "\n" ++ show t2

consCB γ (NonRec x e)
  = do t <- consE γ e
       tg <- generalizeS t
       let ch = tyCheck x ((penv γ) ??= (mkSymbol x)) tg
       if (not ch)  then (return $ γ += (mkSymbol x, tg)) else (return γ)

consCB γ (Rec xes) 
  = do ts       <- mapM (\e -> freshTy $ exprType e) es
       let γ'   = foldl' (+=) γ (zip vs ts)
       zipWithM_ (cconsE γ') es ts
       tsg   <-forM ts generalizeS
       return $ foldl' (+=) γ (zip vs tsg)
    where (xs, es) = unzip xes
          vs       = mkSymbol <$> xs

consE γ (Var x)
  = do t<- γ ?= (mkSymbol x)
       return t
consE _ e@(Lit c) 
  = do t <- freshTy τ
       return t
   where τ = exprType e

consE γ (App e (Type τ)) 
  = do RAll (RV α) te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       let t = trueTy τ
       return $ (α, t, τ) `subsTyVars_` te 
--     $ traceShow ("consE TyA " ++ show α ++ show (varUnique α) ++ " with " ++ show t ++ " in " ++ show te ) 
          

consE γ (App e a)               
  = do RFun (RB x) tx t <- liftM (checkFun ("PNon-fun App with caller", e)) $ consE γ e 
       cconsE γ a tx 
       case argExpr a of 
         Just e  -> return $ {-traceShow "App" $-} (x, e) `substSym` t
         Nothing -> error $ "consE: App crashes on" ++ showPpr a 

consE γ (Lam α e) | isTyVar α 
  = liftM (RAll (RV α)) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy τx 
       t1     <- consE (γ += (mkSymbol x, tx)) e1
       return $ RFun (RB (mkSymbol x)) tx t1
    where FunTy τx _ = exprType e 

consE γ e@(Let _ _)       
  = cconsFreshE γ e

consE γ e@(Case _ _ _ _) 
  = cconsFreshE γ e

consE γ (Tick tt e)      
  = consE (γ `atLoc` tickSrcSpan tt) e

consE γ (Cast e _)      
  = consE γ e 

consE _ e	    
  = error $ "consE cannot handle " ++ showPpr e

cconsFreshE γ e
  = do t   <- freshTy $ exprType e
       cconsE γ e t
       return t

argExpr (Var vy)         = Just $ mkSymbol vy
argExpr (Lit c)          = Just $ stringSymbol "?"
argExpr (Tick _ e)		 = argExpr e
argExpr e                = error $ "argExpr: " ++ (showPpr e)


cconsE γ (Let b e) t    
  = do γ'  <- consCB' γ b
       cconsE γ' e t 

cconsE γ (Case e x τ cases) t 
  = do γ'  <- consCB' γ $ NonRec x e
       forM_ cases $ cconsCase γ' x t

cconsE γ (Lam α e) (RAll (RV _) t) | isTyVar α
  = cconsE γ e t

cconsE γ (Lam x e) (RFun (RB y) ty t) 
  | not (isTyVar x) 
  = do cconsE (γ += (mkSymbol x, ty)) e te 
       addId y (mkSymbol x)
    where te = (y, mkSymbol x) `substSym` t

cconsE γ (Tick tt e) t     
  = cconsE (γ `atLoc` tickSrcSpan tt) e t

cconsE γ (Cast e _) t     
  = cconsE γ e t 

cconsE γ e t 
  = do te <- consE γ e
       addC $ SubC γ te t

cconsCase γ _ t (DEFAULT, _, ce)
--  = cconsE γ ce t
  = return ()

cconsCase γ x t (DataAlt c, ys, ce)
  = do tx <- γ ?= mkSymbol x
       tc <- γ ?= (mkSymbol (TC.dataConWorkId c))
       let (yts, xtt) = unfold tc tx ce
       addC $ SubC γ xtt tx
--       addC $ SubC γ xtt tx
       let cbs = zip (mkSymbol <$> ys) yts
       let cγ = foldl' (+=) γ cbs
       cconsE cγ ce t



unfold tc (RApp _ ts _ _) _ = splitArgsRes tc''
  where (vs, _, tc') = splitVsPs tc
        tc''         = foldl' (flip subsTyVars) tc' (zip vs ts) 
        -- args         = [(α, α') | (α, PrVar α' _) <- zip vs ts]
-- unfold tc _       = splitArgsRes tc'
--  where (vs, _, tc') = splitVsPs tc
unfold tc t               x  = error $ "unfold" ++ {-(showSDoc (ppr x)) ++-} " : " ++ show t

splitC (SubC γ (RAll (RV _) t1) (RAll (RV _) t2))
  = splitC (SubC γ t1 t2)

splitC (SubC γ (RAll (RP _) t1) (RAll (RP _) t2))
  = splitC (SubC γ t1 t2)

splitC (SubC γ (RFun (RB x1) t11 t12) (RFun (RB x2) t21 t22))
  = splitC (SubC γ t21 t11) ++ splitC (SubC γ' t12' t22)
    where t12' = (x1, x2) `substSym` t12
          γ'   = γ += (x2, t21)

splitC (SubC γ (RVar (RV a) p1) (RVar (RV a2) p2))        -- UNIFY: Check a == a2?
  = [splitBC p1 p2]

splitC (SubC γ (RApp c1 ts1 ps1 p1) (RApp c2 ts2 ps2 p2)) -- UNIFY: Check c1 == c2?
  = (concatMap splitC (zipWith (SubC γ) ts1 ts2)) 
    ++ [splitBC x y | (x, y) <- zip ps1 ps2] 
    ++ [splitBC p1 p2]

splitC t@(SubC _ t1 t2)
  = {-traceShow ("WARNING : SubC" ++ show t1 ++ show t2) $-} []

-- UNIFYHERE1: Make output [(PVar t, Predicate t)]
splitBC (Pr []) (Pr []) = []
splitBC (Pr []) p2      = [(p2, pdTrue)] 
splitBC p1      p2      = [(p1, p2)]

addC c@(SubC _ t1 t2) = modify $ \s -> s {hsCsP = c : (hsCsP s)}

addPredApp γ (NonRec b e) = NonRec b $ thrd $ pExpr γ e
addPredApp γ (Rec ls)     = Rec $ zip xs es'
  where es' = (thrd. pExpr γ) <$> es
        (xs, es) = unzip ls

thrd (_, _, x) = x

pExpr γ e 
  = if (a == 0 && p /= 0) 
     then (0, 0, foldl App e' ps) 
     else (0, p, e')
 where  (a, p, e') = pExprN γ e
        ps = (\n -> stringArg ("p" ++ show n)) <$> [1 .. p]

pExprN γ (App e1 e2) = 
  let (a2, p2, e2') = pExprN γ e2 in 
  if (a1 == 0)
   then (0, 0, (App (foldl App e1' ps) e2'))
   else (a1-1, p1, (App e1' e2'))
 where ps = (\n -> stringArg ("p" ++ show n)) <$> [1 .. p1]
       (a1, p1, e1') = pExprN γ e1

pExprN γ (Lam x e) = (0, 0, Lam x e')
  where (_, _, e') = pExpr γ e

pExprN γ (Var v) | isSpecialId γ v
  = (a, p, (Var v))
    where (a, p) = varPredArgs γ v

pExprN γ (Var v) = (0, 0, Var v)

pExprN γ (Let (NonRec x1 e1) e) = (0, 0, Let (NonRec x1 e1') e')
 where (_, _, e') = pExpr γ e
       (_, _, e1') = pExpr γ e1


pExprN γ (Let bds e) = (0, 0, Let bds' e')
 where (_, _, e') = pExpr γ e
       bds' = addPredApp γ bds
pExprN γ (Case e b t es) = (0, 0, Case e' b t (map (pExprNAlt γ ) es))
  where e' = thrd $ pExpr γ e

pExprN γ (Tick n e) = (a, p, Tick n e')
 where (a, p, e') = pExprN γ e

pExprN γ e@(Type _) = (0, 0, e)
pExprN γ e@(Lit _) = (0, 0, e)
pExprN γ e = (0, 0, e)

pExprNAlt γ (x, y, e) = (x, y, e')
 where e' = thrd $ pExpr γ e

stringArg s = Var $ mkGlobalVar idDet name predType idInfo
  where  idDet = coVarDetails
         name  = mkInternalName initTyVarUnique occ noSrcSpan
         occ = mkTyVarOcc s 
         idInfo = vanillaIdInfo

isSpecialId γ x = pl /= 0
  where (_, pl) = varPredArgs γ x
varPredArgs γ x = varPredArgs_ (γ ??= (mkSymbol x))
varPredArgs_ Nothing = (0, 0)
varPredArgs_ (Just t) = (length vs, length ps)
  where (vs, ps, _) = splitVsPs t

trueTy = ofTypeP

generalizeS t 
  = do splitCons
       s <- pMap <$> get 
       return $ {-traceShow ("GENERALIZE " ++ show t ++ " with " ++ show s) $-} generalize $ subp s t

getRemoveHsCons 
  = do s <- get
       let cs = hsCsP s
       put s { hsCsP = [] }
       return cs

-- UNIFYHERE2: normalize m to make sure RHS does not contain LHS Var,

addToMap substs 
  = do s <- get
       let m  = pMap s
       let m' = foldl' updateSubst m substs
       put $ s { pMap = m' }

updateSubst :: M.Map (PVar Type) (Predicate Type) -> (Predicate Type, Predicate Type) -> M.Map (PVar Type) (Predicate Type) 
updateSubst m (p, p') = foldl' (\m (k, v) -> M.insert k v m) m binds 
  where binds = unifiers $ unifyVars (subp m p) (subp m p')

unifyVars (Pr v1s) (Pr v2s) = (v1s L.\\ vs, v2s L.\\ vs) 
  where vs  = L.intersect v1s v2s

unifiers ([], vs') = [(v', pdTrue) | v' <- vs']
unifiers (vs, vs') = [(v , Pr vs')      | v  <- vs ]

splitCons :: PI () 
splitCons
  = do hsCs <- getRemoveHsCons
       addToMap ((concat (concatMap splitC hsCs)))

-- generalize predicates of arguments: used on Rec Definitions

initEnv info = PCGE { loc = noSrcSpan , penv = F.fromListSEnv bs}
  where dflts  = [(x, trueTy $ varType x) | x <- freeVs]
        dcs    = [(x, dconTy $ varType x) | x <- dcons]
        sdcs   = map (\(x, t) -> (TC.dataConWorkId x, dataConPtoPredTy t)) (dconsP info)
        assms  = passm info
        bs     =  mapFst mkSymbol <$> (dflts ++ dcs ++ assms ++ sdcs)
        freeVs = [v | v<-importVars $ cbs info]
        dcons  = filter isDataCon freeVs



getNeedPd info 
  = F.fromListSEnv bs
    where  dcs = map (\(x, t) -> (TC.dataConWorkId x, dataConPtoPredTy t)) (dconsP info)
           assms = passm info
           bs = mapFst mkSymbol <$> (dcs ++ assms)

dconTy t = generalize $ dataConTy vps t
  where vs  = tyVars t
        ps  = truePr <$> vs 
        vps = M.fromList $ zipWith (\(TyVarTy v) p -> (v, RVar (RV v) p)) vs ps

tyVars (ForAllTy v t) = (TyVarTy v):(tyVars t)
tyVars t              = []

---------------------------------- Freshness -------------------------------------
freshInt = do pi <- get 
              let n = freshIndex pi
              put $ pi {freshIndex = n+1} 
              return n

stringSymbol  = F.S
freshSymbol s = stringSymbol . (s ++ ) . show <$> freshInt
freshPr a     = (\sy -> pdVar (PV sy a [])) <$> (freshSymbol "p")
truePr _      = pdTrue

freshPrAs p = (\n -> pdVar $ p { pname = n }) <$> freshSymbol "p"

refreshTy t 
  = do fps <- mapM freshPrAs ps
       return $ subp (M.fromList (zip ps fps)) t''
   where (vs, ps, t') = splitVsPs t
         t''          = typeAbsVsPs t' vs []

freshTy t 
  | isPredTy t
  = return $ freshPredTree $ (classifyPredType t)
freshTy t@(TyVarTy v) 
  = liftM (RVar (RV v)) (freshPr t)
freshTy (FunTy t1 t2) 
  = liftM3 RFun (RB <$> freshSymbol "s") (freshTy t1) (freshTy t2)
freshTy t@(TyConApp c τs) 
  | TyCon.isSynTyCon c
  = freshTy $ substTyWith αs τs τ
  where (αs, τ) = TyCon.synTyConDefn c
freshTy t@(TyConApp c τs) 
  = liftM3 (rApp c) (mapM freshTy τs) (freshTyConPreds c) (return (truePr t)) 
freshTy (ForAllTy v t) 
  = liftM (RAll (RV v)) (freshTy t) 
freshTy t
  = error "freshTy"

freshPredTree (ClassPred c ts)
  = RCls c (trueTy <$> ts)

freshTyConPreds c 
 = do s <- get
      case (M.lookup c (tyCons s)) of 
       Just x  -> mapM freshPrAs (freePredTy x)
       Nothing -> return []

checkFun _ t@(RFun _ _ _) = t
checkFun x t              = error $ showPpr x ++ "type: " ++ showPpr t

checkAll _ t@(RAll (RV _) _) = t
checkAll x t                 = error $ showPpr x ++ "type: " ++ showPpr t

γ `atLoc` src
  | isGoodSrcSpan src = γ { loc = src } 
  | otherwise = γ
