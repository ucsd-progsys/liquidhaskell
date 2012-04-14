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

import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.PredType
import Language.Haskell.Liquid.GhcMisc2 (stringTyVar, tickSrcSpan)
import Language.Haskell.Liquid.RefType (mkSymbol)
import Language.Haskell.Liquid.Misc
import qualified Language.Haskell.Liquid.Fixpoint as F

import Control.Monad.State
import Control.Applicative      ((<$>))
import qualified Data.Map as M
import qualified Data.List as L
import Data.List (foldl')

predType :: Type
predType = TyVarTy $ stringTyVar "Pred"

consAct info 
  = do γ  <- initEnv info
       γ1 <- foldM consCB γ $ cbs info
       return γ1

generatePredicates info = trace ("Predicates\n" ++ show γ ++ show cbs') (cbs', γ)
  where γ    = mapPEnv removeExtPreds $ penv $ evalState act (initPI info)
        act  = consAct info
        cbs' = addPredApp γ <$> cbs info

instance Show CoreBind where
  show = showSDoc . ppr

γ += (x, t) = γ{ penv = insertPEnv (x, t) (penv γ)}
γ ??= x = lookupPEnv x γ


γ ?= x 
  = case (lookupPEnv x (penv γ)) of 
      Just t  -> refreshTy t
      Nothing -> error $ "PEnvlookupR: unknown = " ++ showPpr x

data PCGEnv = PCGE { loc :: !SrcSpan
								           , penv :: !PEnv
                   }

data PInfo   = PInfo { freshIndex :: !Integer
                     , pMap       :: !(M.Map Predicate Predicate)
                     , hsCsP       :: ![SubC]
										           , tyCons     :: !(M.Map TyCon TyConP)
																					, symbolsP   :: !(M.Map F.Symbol F.Symbol)
                     }

data SubC    = SubC { senv :: !PCGEnv
                    , lhs  :: !PrType
                    , rhs  :: !PrType
                    }

addId x y= modify $ \s -> s{symbolsP = M.insert x y (symbolsP s)}


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


consCB γ (NonRec x e)
  = do t <- consE γ e
       tg <- generalizeS t
       return $ γ += (mkSymbol x, tg)


consCB γ (Rec xes) 
  = do ts       <- mapM (\e -> freshTy $ exprType e) es
--       let tsga = generalizeArgs <$> ts
       let γ'   = foldl' (+=) γ (zip vs ts)
       zipWithM_ (cconsE γ') es ts
       tsg   <-forM ts generalizeS
       return $ foldl' (+=) γ (zip vs tsg)
    where (xs, es) = unzip xes
          vs       = mkSymbol <$> xs

consE γ (Var x)
  = do t<- γ ?= (mkSymbol x)
       return $ traceShow ("consE Var" ++ show x) t
consE _ e@(Lit c) 
  = do t <- freshTy τ
       return t
   where τ = exprType e

consE γ (App e (Type τ)) 
  = do PrAll α te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       t          <- trueTy τ
       return  $ {-traceShow ("consE TyA " ++ show α ++ " with " ++ show t ++ " in " ++ show te ) $-}  (α, t) `subsTyVars` te

consE γ (App e a)               
  = do PrFun x tx t <- liftM (checkFun ("PNon-fun App with caller", e)) $ consE γ e 
       cconsE γ a tx 
       case argExpr a of 
         Just e  -> return $ {-traceShow "App" $-} (x, e) `substSym` t
         Nothing -> error $ "consE: App crashes on" ++ showPpr a 

consE γ (Lam α e) | isTyVar α 
  = liftM (PrAll α) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy τx 
       t1     <- consE (γ += (mkSymbol x, tx)) e1
       return $ PrFun (mkSymbol x) tx t1
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

cconsE γ (Lam α e) (PrAll _ t) | isTyVar α
  = cconsE γ e t

cconsE γ (Lam x e) (PrFun y ty t) 
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

unfold tc (PrTyCon _ ts _ _) _ = splitArgsRes tc''
  where (vs, _, tc') = splitVsPs tc
        tc''         = foldl' (flip subsTyVars) tc' (zip vs ts)
-- unfold tc _                  = splitArgsRes tc'
--  where (vs, _, tc') = splitVsPs tc
unfold tc t               x  = error $ "unfold" ++ {-(showSDoc (ppr x)) ++-} " : " ++ show t

splitC (SubC γ (PrAll _ t1) (PrAll _ t2))
  = splitC (SubC γ t1 t2)

splitC (SubC γ (PrAllPr _ t1) (PrAllPr _ t2))
  = splitC (SubC γ t1 t2)

splitC (SubC γ (PrFun x1 t11 t12) (PrFun x2 t21 t22))
  = splitC (SubC γ t21 t11) ++ splitC (SubC γ' t12' t22)
    where t12' = (x1, x2) `substSym` t12
          γ'   = γ += (x2, t21)

splitC (SubC γ (PrVar a p1) (PrVar a2 p2))
  = [splitBC γ p1 p2]

splitC (SubC γ (PrTyCon c1 ts1 ps1 p1) (PrTyCon c2 ts2 ps2 p2))
  = (concatMap splitC (zipWith (SubC γ) ts1 ts2))++ map (\(x, y) -> splitBC γ x y) (zip ps1 ps2) ++ [splitBC γ p1 p2]

splitC t@(SubC _ t1 t2)
  = {-traceShow ("WARNING : SubC" ++ show t1 ++ show t2) $-} []

splitBC γ PdTrue PdTrue = []
splitBC γ PdTrue p2     = [(p2, PdTrue)]
splitBC γ p1     p2     = [(p1, p2)]


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
 where (_, _, e') = pExprN γ e
       (_, _, e1') = pExprN γ e1


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

trueTy = return . ofTypeP

generalizeS t 
  = do splitCons
       s <- getPMap
       return $ {-traceShow ("GENERALIZE " ++ show t ++ " with " ++ show s) $-} generalize $ subp s t

getPMap   = get >>= return . pMap

getRemoveHsCons 
  = do s <- get
       let cs = hsCsP s
       put s{hsCsP = []}
       return cs

addToMap m -- = --modify $ \s -> s{pMap = (pMap s) `M.union` (M.fromList m)}
  = do s <- get
       let m' = foldl foo (M.toList (pMap s)) m
       put s{pMap = M.fromList m'}

foo m kv@(k, v) 
  = kv':(map (rpl kv') m)
   where k' = case (L.lookup k m) of 
               Nothing -> k
               Just k' -> k'
         v' = case (L.lookup v m) of 
               Nothing -> v
               Just v' -> v'
         kv' = case k' of 
                PdTrue -> (v', k')
                _      -> (k', v')
rpl (k, v) (k', v')
  | k == k'
  = (v, v')
  | k == v'
  = (k', v)
  | otherwise 
  = (k', v')

splitCons :: PI () 
splitCons
  = do hsCs <- getRemoveHsCons
       addToMap ((concat (concatMap splitC hsCs)))

-- generalize predicates of arguments
-- used on Rec Definitions


initEnv :: GhcInfo -> PI PCGEnv
initEnv info 
  = do defaults <- forM freeVars $ \x -> liftM (x,) (trueTy $ varType x)
       dcs      <- forM dcons    $ \x -> liftM (x,) (dconTy $ varType x)
       let sdcs = traceShow "dataCon Tys" $ map (\(x, t) -> (TC.dataConWorkId x, dataConPtoPredTy t)) (dconsP info)
       let assms = passm info
       let bs =  mapFst mkSymbol <$> (defaults ++ dcs ++ assms ++ sdcs)
       return $ PCGE { loc = noSrcSpan , penv = fromListPEnv bs}
    where freeVars = [v | v<-importVars $ cbs info]
          dcons = filter isDataCon freeVars

dconTy t
  = do ps <- mapM truePr vs
       let vps = M.fromList $ zipWith (\(TyVarTy v) p -> (v, PrVar v p)) vs ps
       return $ generalize $ dataConTy vps t
		where vs = tyVars t


tyVars (ForAllTy v t) = (TyVarTy v):(tyVars t)
tyVars t                        = []
---------------------------------- Freshness -------------------------------------
freshInt = do pi <- get 
              let n = freshIndex pi
              put $ pi {freshIndex = n+1} 
              return n

freshPrAs p = freshInt >>= \n -> return $ p{pname = "p" ++ (show n)}
stringSymbol = F.S
refreshTy t 
  = do fps <- mapM freshPrAs ps
       return $ traceShow ("Ps vs FPs" ++ show (ps, fps)) $ subp (M.fromList (zip ps fps)) t''
   where (vs, ps, t') = splitVsPs t
         t''          = typeAbsVsPs t' vs []

truePr a = return PdTrue
freshPr a = do n <- freshInt
               return $ PdVar {pname = "p" ++ (show n), ptype = a, pargs = []}

freshSymbol = do n <- freshInt
                 return $ stringSymbol $ "s" ++ (show n)
freshTy t
  | isPredTy t
  = freshPredTree $ classifyPredType t
freshTy t@(TyVarTy v) = freshPr t >>= \p -> return $ PrVar v p
freshTy (FunTy t1 t2) = do tt1 <- freshTy t1
                           tt2 <- freshTy t2
                           s <- freshSymbol
                           return $ PrFun s tt1 tt2
freshTy t@(TyConApp c τs) | TyCon.isSynTyCon c
  = freshTy $ substTyWith αs τs τ
 where (αs, τ) = TyCon.synTyConDefn c
freshTy t@(TyConApp c τs) = do ts <- mapM trueTy τs
                               p  <- truePr t
                               ps <- freshTyConPreds c
                               return $ PrTyCon c ts ps p
freshTy (ForAllTy c t) = freshTy t >>= \τ -> return $ PrAll c τ
freshTy t
  = error "freshTy"

freshPredTree (ClassPred c ts)
  = liftM (PrClass c) (mapM trueTy ts)

freshTyConPreds c 
 = do s <- get
      case (M.lookup c (tyCons s)) of 
       Just x  -> mapM freshPrAs (freePredTy x)
       Nothing -> return []

checkFun _ t@(PrFun _ _ _) = t
checkFun x t               = error $ showPpr x ++ "type: " ++ showPpr t

checkAll _ t@(PrAll _ _)   = t
checkAll x t               = error $ showPpr x ++ "type: " ++ showPpr t

γ `atLoc` src
  | isGoodSrcSpan src = γ { loc = src } 
  | otherwise = γ

