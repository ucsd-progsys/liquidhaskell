{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE ScopedTypeVariables        #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Relational (consAssmRel, consRelTop) where

import           Control.Monad.State
import           Data.Bifunctor                                 ( Bifunctor(bimap) )
import qualified Data.HashMap.Strict                            as M
import qualified Data.List                                      as L
import           Data.String                                    ( IsString(..) )
import qualified Language.Fixpoint.Types                        as F
import qualified Language.Fixpoint.Types.Visitor                as F
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Types
import           Liquid.GHC.API                 ( Alt
                                                , AltCon(..)
                                                , Bind(..)
                                                , CoreBind
                                                , CoreBndr
                                                , CoreExpr
                                                , Expr(..)
                                                , Type(..)
                                                , TyVar
                                                , Var(..))
import qualified Liquid.GHC.API                as Ghc
import qualified Liquid.GHC.Misc               as GM
import           Liquid.GHC.Play               (Subable(sub, subTy))
import qualified Liquid.GHC.SpanStack          as Sp
import           Liquid.GHC.TypeRep            ()
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types                  hiding (Def,
                                                                 Loc, binds,
                                                                 loc)
import           System.Console.CmdArgs.Verbosity               (whenLoud)
import           System.IO.Unsafe                               (unsafePerformIO)

data RelPred
  = RelPred { fun1 :: Var
            , fun2 :: Var
            , args1 :: [(F.Symbol, [F.Symbol])]
            , args2 :: [(F.Symbol, [F.Symbol])]
            , prop :: RelExpr
            } deriving Show

type PrEnv = [RelPred]

consAssmRel :: Config -> TargetInfo -> (PrEnv, CGEnv) -> (Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr) -> CG (PrEnv, CGEnv)
consAssmRel _ _ (ψ, γ) (x, y, t, s, _, rp) = traceChk "Assm" x y t s p $ do
  traceWhenLoud ("ASSUME " ++ F.showpp (fromRelExpr p', p)) $ subUnarySig γ' x t'
  subUnarySig γ' y s'
  γ'' <- if base t' && base s'
    then γ' `addPred` F.subst
      (F.mkSubst [(resL, F.EVar $ F.symbol x), (resR, F.EVar $ F.symbol y)])
      (fromRelExpr rp)
    else return γ'
  return (RelPred x' y' bs cs rp : ψ, γ'')
 where
    p = fromRelExpr rp
    γ' = γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc t))
    (x', y') = mkRelCopies x y
    t' = val t
    s' = val s
    (vs, ts) = vargs t'
    (us, ss) = vargs s'
    bs = zip vs (fst . vargs <$> ts)
    cs = zip us (fst . vargs <$> ss)
    p' = L.foldl (\q (v, u) -> unapplyRelArgsR v u q) rp (zip vs us)

consRelTop :: Config -> TargetInfo -> CGEnv -> PrEnv -> (Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr) -> CG ()
consRelTop _ ti γ ψ (x, y, t, s, ra, rp) = traceChk "Init" e d t s p $ do
  subUnarySig γ' x t'
  subUnarySig γ' y s'
  consRelCheckBind γ' ψ e d t' s' ra rp
  where
    p = fromRelExpr rp
    γ' = γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc t))
    cbs = giCbs $ giSrc ti
    e = lookupBind x cbs
    d = lookupBind y cbs
    t' = removeAbsRef $ val t
    s' = removeAbsRef $ val s

removeAbsRef :: SpecType -> SpecType
removeAbsRef (RVar v (MkUReft r _)) 
  = out
    where 
      r' = MkUReft r mempty
      out = RVar  v r' 
removeAbsRef (RFun  b i s t (MkUReft r _))  
  = out
    where 
      r' = MkUReft r mempty
      out = RFun  b i (removeAbsRef s) (removeAbsRef t) r'
removeAbsRef (RImpF b i s t (MkUReft r _))  
  = out
    where 
      r' = MkUReft r mempty
      out = RImpF b i (removeAbsRef s) (removeAbsRef t) r'
removeAbsRef (RAllT b t r)      
  = RAllT b (removeAbsRef t) r
removeAbsRef (RAllP p t)        
  = removeAbsRef (forgetRAllP p t)
removeAbsRef (RApp  (RTyCon c _ i) as _ (MkUReft r _))   
  = out
    where 
      c' = RTyCon c [] i
      as' = map removeAbsRef as
      r' = MkUReft r mempty
      out = RApp c' as' [] r'
removeAbsRef (RAllE b a t)      
  = RAllE b (removeAbsRef a) (removeAbsRef t)
removeAbsRef (REx   b a t)      
  = REx   b (removeAbsRef a) (removeAbsRef t)
removeAbsRef (RAppTy s t r)     
  = RAppTy (removeAbsRef s) (removeAbsRef t) r
removeAbsRef (RRTy  e r o t)    
  = RRTy  e r o (removeAbsRef t)
removeAbsRef t 
  = t

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

resL, resR :: F.Symbol
resL = fromString "r1"
resR = fromString "r2"

relSuffixL, relSuffixR :: String
relSuffixL = "l"
relSuffixR = "r"

-- recursion rule
consRelCheckBind :: CGEnv -> PrEnv -> CoreBind -> CoreBind -> SpecType -> SpecType -> RelExpr -> RelExpr -> CG ()
consRelCheckBind γ ψ b1@(NonRec _ e1) b2@(NonRec _ e2) t1 t2 ra rp
  | Nothing <- args e1 e2 t1 t2 p =
  traceChk "Bind NonRec" b1 b2 t1 t2 p $ do
    γ' <- γ `addPred` a
    consRelCheck γ' ψ e1 e2 t1 t2 p
  where
    a = fromRelExpr ra
    p = fromRelExpr rp

consRelCheckBind γ ψ (NonRec x1 e1) b2 t1 t2 a p =
  consRelCheckBind γ ψ (Rec [(x1, e1)]) b2 t1 t2 a p

consRelCheckBind γ ψ b1 (NonRec x2 e2) t1 t2 a p =
  consRelCheckBind γ ψ b1 (Rec [(x2, e2)]) t1 t2 a p

consRelCheckBind γ ψ b1@(Rec [(f1, e1)]) b2@(Rec [(f2, e2)]) t1 t2 ra rp
  | Just (xs1, xs2, vs1, vs2, ts1, ts2, qs) <- args e1 e2 t1 t2 p
  = traceChk "Bind Rec" b1 b2 t1 t2 p $ do
    forM_ (refts t1 ++ refts t2) (\r -> entlFunReft γ r "consRelCheckBind Rec")
    let xs' = zipWith mkRelCopies xs1 xs2
    let (xs1', xs2') = unzip xs'
    let (e1'', e2'') = L.foldl' subRel (e1', e2') (zip xs1 xs2)
    γ' <- γ += ("Bind Rec f1", F.symbol f1', t1) >>= (+= ("Bind Rec f2", F.symbol f2', t2))
    γ'' <- foldM (\γγ (x, t) -> γγ += ("Bind Rec x1", F.symbol x, t)) γ' (zip (xs1' ++ xs2') (ts1 ++ ts2))
    let vs2xs =  F.subst $ F.mkSubst $ zip (vs1 ++ vs2) $ map (F.EVar . F.symbol) (xs1' ++ xs2')
    let (ho, fo) = partitionArgs xs1 xs2 ts1 ts2 qs
    γ''' <- γ'' `addPreds` traceWhenLoud ("PRECONDITION " ++ F.showpp (vs2xs (F.PAnd fo)) ++ "\n" ++
                                          "ASSUMPTION " ++ F.showpp (vs2xs a))
                              map vs2xs [F.PAnd fo, a]
    let p' = unapp rp (zip vs1 vs2)
    let ψ' = ho ++ ψ
    consRelCheck γ''' ψ' (xbody e1'') (xbody e2'') (vs2xs $ ret t1) (vs2xs $ ret t2) (vs2xs $ concl (fromRelExpr p'))
  where
    a = fromRelExpr ra
    p = fromRelExpr rp
    (f1', f2') = mkRelCopies f1 f2
    (e1', e2') = subRelCopies e1 f1 e2 f2
    unapp :: RelExpr -> [(F.Symbol, F.Symbol)] -> RelExpr
    unapp = L.foldl' (\p' (v1, v2) -> unapplyRelArgsR v1 v2 p')
    subRel (e1'', e2'') (x1, x2) = subRelCopies e1'' x1 e2'' x2

consRelCheckBind _ _ (Rec [(_, e1)]) (Rec [(_, e2)]) t1 t2 _ rp
  = F.panic $ "consRelCheckBind Rec: exprs, types, and pred should have same number of args " ++
    show (args e1 e2 t1 t2 p)
    where
      p = fromRelExpr rp

consRelCheckBind _ _ b1@(Rec _) b2@(Rec _) _ _ _ _
  = F.panic $ "consRelCheckBind Rec: multiple binders are not supported " ++ F.showpp (b1, b2)

consRelCheck :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr ->
  SpecType -> SpecType -> F.Expr -> CG ()
consRelCheck γ ψ (Tick tt e) d t s p =
  consRelCheck (γ `setLocation` Sp.Tick tt) ψ e d t s p

consRelCheck γ ψ e (Tick tt d) t s p =
  consRelCheck (γ `setLocation` Sp.Tick tt) ψ e d t s p

consRelCheck γ ψ l1@(Lam α1 e1) e2 rt1@(RAllT s1 t1 r1) t2 p
  | Ghc.isTyVar α1
  = traceChk "Lam Type L" l1 e2 rt1 t2 p $ do
    entlFunReft γ r1 "consRelCheck Lam Type"
    γ'  <- γ `extendWithTyVar` α1
    consRelCheck γ' ψ e1 e2 (sb (s1, α1) t1) t2 p
  where sb (s, α) = subsTyVarMeet' (ty_var_value s, rVar α)

consRelCheck γ ψ e1 l2@(Lam α2 e2) t1 rt2@(RAllT s2 t2 r2) p
  | Ghc.isTyVar α2
  = traceChk "Lam Type" e1 l2 t1 rt2 p $ do
    entlFunReft γ r2 "consRelCheck Lam Type"
    γ'  <- γ `extendWithTyVar` α2
    consRelCheck γ' ψ e1 e2 t1 (sb (s2, α2) t2) p
  where sb (s, α) = subsTyVarMeet' (ty_var_value s, rVar α)

consRelCheck γ ψ l1@(Lam α1 e1) l2@(Lam α2 e2) rt1@(RAllT s1 t1 r1) rt2@(RAllT s2 t2 r2) p
  | Ghc.isTyVar α1 && Ghc.isTyVar α2
  = traceChk "Lam Type" l1 l2 rt1 rt2 p $ do
    entlFunRefts γ r1 r2 "consRelCheck Lam Type"
    γ'  <- γ `extendWithTyVar` α1
    γ'' <- γ' `extendWithTyVar` α2
    consRelCheck γ'' ψ e1 e2 (sb (s1, α1) t1) (sb (s2, α2) t2) p
  where sb (s, α) = subsTyVarMeet' (ty_var_value s, rVar α)

consRelCheck γ ψ l1@(Lam x1 e1) l2@(Lam x2 e2) rt1@(RFun v1 _ s1 t1 r1) rt2@(RFun v2 _ s2 t2 r2) pr@(F.PImp q p)
  = traceChk "Lam Expr" l1 l2 rt1 rt2 pr $ do
    entlFunRefts γ r1 r2 "consRelCheck Lam Expr"
    let (pvar1, pvar2) = (F.symbol evar1, F.symbol evar2)
    let subst = F.subst $ F.mkSubst [(v1, F.EVar pvar1), (v2, F.EVar pvar2)]
    γ'  <- γ += ("consRelCheck Lam L", pvar1, subst s1)
    γ'' <- γ' += ("consRelCheck Lam R", pvar2, subst s2)
    let p'    = unapplyRelArgs v1 v2 p
    let (ho, fo) = partitionArg x1 x2 s1 s2 q
    γ''' <- γ'' `addPreds` traceWhenLoud ("PRECONDITION " ++ F.showpp (map subst fo)) map subst fo
    consRelCheck γ''' (ho ++ ψ) e1' e2' (subst t1) (subst t2) (subst p')
  where
    (evar1, evar2) = mkRelCopies x1 x2
    (e1', e2')     = subRelCopies e1 x1 e2 x2

consRelCheck γ ψ l1@(Let (NonRec x1 d1) e1) l2@(Let (NonRec x2 d2) e2) t1 t2 p
  = traceChk "Let" l1 l2 t1 t2 p $ do
    (s1, s2, _) <- consRelSynth γ ψ d1 d2
    let (evar1, evar2) = mkRelCopies x1 x2
    let (e1', e2')     = subRelCopies e1 x1 e2 x2
    γ'  <- γ += ("consRelCheck Let L", F.symbol evar1, s1)
    γ'' <- γ' += ("consRelCheck Let R", F.symbol evar2, s2)
    consRelCheck γ'' ψ e1' e2' t1 t2 p
  

consRelCheck γ ψ l1@(Let (Rec []) e1) l2@(Let (Rec []) e2) t1 t2 p
  = traceChk "Let Rec Nil" l1 l2 t1 t2 p $ do
    consRelCheck γ ψ e1 e2 t1 t2 p

consRelCheck γ ψ l1@(Let (Rec ((x1, d1):bs1)) e1) l2@(Let (Rec ((x2, d2):bs2)) e2) t1 t2 p
  = traceChk "Let Rec Cons" l1 l2 t1 t2 p $ do
    (s1, s2, _) <- consRelSynth γ ψ d1 d2
    let (evar1, evar2) = mkRelCopies x1 x2
    let (e1', e2')     = subRelCopies e1 x1 e2 x2
    γ'  <- γ += ("consRelCheck Let L", F.symbol evar1, s1)
    γ'' <- γ' += ("consRelCheck Let R", F.symbol evar2, s2)
    consRelCheck γ'' ψ (Let (Rec bs1) e1') (Let (Rec bs2) e2') t1 t2 p

consRelCheck γ ψ c1@(Case e1 x1 _ alts1) e2 t1 t2 p =
  traceChk "Case Async L" c1 e2 t1 t2 p $ do
    s1 <- consUnarySynth γ e1
    γ' <- γ += ("consRelCheck Case Async L", x1', s1)
    forM_ alts1 $ consRelCheckAltAsyncL γ' ψ t1 t2 p x1' s1 e2
  where
    x1' = F.symbol $ mkCopyWithSuffix relSuffixL x1

consRelCheck γ ψ e1 c2@(Case e2 x2 _ alts2) t1 t2 p =
  traceChk "Case Async R" e1 c2 t1 t2 p $ do
    s2 <- consUnarySynth γ e2
    γ' <- γ += ("consRelCheck Case Async R", x2', s2)
    forM_ alts2 $ consRelCheckAltAsyncR γ' ψ t1 t2 p e1 x2' s2
  where
    x2' = F.symbol $ mkCopyWithSuffix relSuffixR x2

consRelCheck γ ψ e d t1 t2 p =
  traceChk "Synth" e d t1 t2 p $ do
  (s1, s2, qs) <- consRelSynth γ ψ e d
  let psubst = F.substf (matchFunArgs t1 s1) . F.substf (matchFunArgs t2 s2)
  consRelSub γ s1 s2 (F.PAnd qs) (psubst p)
  addC (SubC γ s1 t1) ("consRelCheck (Synth): s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γ s2 t2) ("consRelCheck (Synth): s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)

consExtAltEnv :: CGEnv -> F.Symbol -> SpecType -> AltCon -> [Var] -> CoreExpr -> String -> CG (CGEnv, CoreExpr)
consExtAltEnv γ x s c bs e suf = do
  ct <- ctorTy γ c s
  unapply γ x s bs (removeAbsRef ct) e suf

consRelCheckAltAsyncL :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr ->
  F.Symbol -> SpecType -> CoreExpr -> Alt CoreBndr -> CG ()
consRelCheckAltAsyncL γ ψ t1 t2 p x1 s1 e2 (Ghc.Alt c bs1 e1) = do
  (γ', e1') <- consExtAltEnv γ x1 s1 c bs1 e1 relSuffixL
  consRelCheck γ' ψ e1' e2 t1 t2 p

consRelCheckAltAsyncR :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr ->
  CoreExpr -> F.Symbol -> SpecType -> Alt CoreBndr -> CG ()
consRelCheckAltAsyncR γ ψ t1 t2 p e1 x2 s2 (Ghc.Alt c bs2 e2) = do
  (γ', e2') <- consExtAltEnv γ x2 s2 c bs2 e2 relSuffixR
  consRelCheck γ' ψ e1 e2' t1 t2 p

ctorTy :: CGEnv -> AltCon -> SpecType -> CG SpecType
ctorTy γ (DataAlt c) (RApp _ ts _ _)
  | Just ct <- mbct = refreshTy $ ct `instantiateTys` ts
  | Nothing <- mbct = F.panic $ "ctorTy: data constructor out of scope" ++ F.showpp c
  where mbct = γ ?= F.symbol (Ghc.dataConWorkId c)
ctorTy _ (DataAlt _) t =
  F.panic $ "ctorTy: type " ++ F.showpp t ++ " doesn't have top-level data constructor"
ctorTy _ (LitAlt c) _ = return $ uTop <$> literalFRefType c
ctorTy _ DEFAULT t = return t

unapply :: CGEnv -> F.Symbol -> SpecType -> [Var] -> SpecType -> CoreExpr -> String -> CG (CGEnv, CoreExpr)
unapply γ y yt (z : zs) (RFun x _ s t _) e suffix = do
  γ' <- γ += ("unapply arg", evar, s)
  unapply γ' y yt zs (t `F.subst1` (x, F.EVar evar)) e' suffix
  where
    z' = mkCopyWithSuffix suffix z
    evar = F.symbol z'
    e' = subVarAndTy z z' e
unapply _ _ _ (_ : _) t _ _ = F.panic $ "can't unapply type " ++ F.showpp t
unapply γ y yt [] t e _ = do
  let yt' = t `F.meet` yt
  γ' <- γ += ("unapply res", y, yt')
  return $ traceWhenLoud ("SCRUTINEE " ++ F.showpp (y, yt')) (γ', e)

instantiateTys :: SpecType -> [SpecType] -> SpecType
instantiateTys = L.foldl' go
 where
  go (RAllT α tbody _) t = subsTyVarMeet' (ty_var_value α, t) tbody
  go tbody             t =
    F.panic $ "instantiateTys: non-polymorphic type " ++ F.showpp tbody ++ " to instantiate with " ++ F.showpp t

--------------------------------------------------------------
-- Core Synthesis Rules --------------------------------------
--------------------------------------------------------------

consRelSynth :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, [F.Expr])
consRelSynth γ ψ (Tick tt e) d =
  consRelSynth (γ `setLocation` Sp.Tick tt) ψ e d

consRelSynth γ ψ e (Tick tt d) =
  consRelSynth (γ `setLocation` Sp.Tick tt) ψ e d

consRelSynth γ ψ a1@(App e1 d1) e2 | Type t1 <- GM.unTickExpr d1 =
  traceSyn "App Ty L" a1 e2 $ do
    (ft1', t2, ps) <- consRelSynth γ ψ e1 e2
    let (α1, ft1, _) = unRAllT ft1' "consRelSynth App Ty L"
    t1' <- trueTy (typeclass (getConfig γ)) t1
    return (subsTyVarMeet' (ty_var_value α1, t1') ft1, t2, ps)

consRelSynth γ ψ e1 a2@(App e2 d2) | Type t2 <- GM.unTickExpr d2 =
  traceSyn "App Ty R" e1 a2 $ do
    (t1, ft2', ps) <- consRelSynth γ ψ e1 e2
    let (α2, ft2, _) = unRAllT ft2' "consRelSynth App Ty R"
    t2' <- trueTy (typeclass (getConfig γ)) t2
    return (t1, subsTyVarMeet' (ty_var_value α2, t2') ft2, ps)

consRelSynth γ ψ a1@(App e1 d1) a2@(App e2 d2) = traceSyn "App Exp Exp" a1 a2 $ do
  (ft1, ft2, fps) <- consRelSynth γ ψ e1 e2
  (t1, t2, ps) <- consRelSynthApp γ ψ ft1 ft2 fps d1 d2
  return (t1, t2, ps)

consRelSynth γ ψ e d = traceSyn "Unary" e d $ do
  t <- consUnarySynth γ e >>= refreshTy
  s <- consUnarySynth γ d >>= refreshTy
  let ps = lookupRelSig ψ e d t s
  return (t, s, traceWhenLoud ("consRelSynth Unary synthed preds:" ++ F.showpp ps) ps)
    
lookupRelSig :: PrEnv -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> [F.Expr] 
lookupRelSig ψ (Var x1) (Var x2) t1 t2 = concatMap match ψ
  where 
    match :: RelPred -> [F.Expr]
    match (RelPred f1 f2 bs1 bs2 p) | f1 == x1, f2 == x2 = 
        let (vs1, ts1') = vargs t1
            (vs2, ts2') = vargs t2
            vs1' = concatMap (fst . vargs) ts1'
            vs2' = concatMap (fst . vargs) ts2'
            bs1' = concatMap snd bs1
            bs2' = concatMap snd bs2
            bs2vs = F.mkSubst $ zip (map fst bs1 ++ map fst bs2 ++ bs1' ++ bs2') $ map F.EVar (vs1 ++ vs2 ++ vs1' ++ vs2')
          in [F.subst bs2vs (fromRelExpr p)]
    match _ = []
lookupRelSig _ _ _ _ _ = []

consRelSynthApp :: CGEnv -> PrEnv -> SpecType -> SpecType ->
  [F.Expr] -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, [F.Expr])
consRelSynthApp γ ψ ft1 ft2 ps e1 (Tick _ e2) =
  consRelSynthApp γ ψ ft1 ft2 ps e1 e2
consRelSynthApp γ ψ ft1 ft2 ps (Tick t1 e1) e2 =
  consRelSynthApp (γ `setLocation` Sp.Tick t1) ψ ft1 ft2 ps e1 e2

consRelSynthApp γ ψ ft1@(RFun v1 _ s1 t1 r1) ft2@(RFun v2 _ s2 t2 r2) ps@[F.PImp q p] d1@(Var x1) d2@(Var x2)
  = traceSynApp ft1 ft2 ps d1 d2 $ do
    entlFunRefts γ r1 r2 "consRelSynthApp HO"
    let qsubst = F.subst $ F.mkSubst [(v1, F.EVar resL), (v2, F.EVar resR)]
    consRelCheck γ ψ d1 d2 s1 s2 (qsubst q)
    let subst = F.subst $ F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
    return (subst t1, subst t2, [(subst . unapplyRelArgs v1 v2) p])
consRelSynthApp γ ψ ft1@(RFun v1 _ s1 t1 r1) ft2@(RFun v2 _ s2 t2 r2) ps@[] d1@(Var x1) d2@(Var x2)
  = traceSynApp ft1 ft2 ps d1 d2 $ do
    entlFunRefts γ r1 r2 "consRelSynthApp FO"
    consUnaryCheck γ d1 s1
    consUnaryCheck γ d2 s2
    (_, _, qs) <- consRelSynth γ ψ d1 d2
    let subst =
          F.subst $ F.mkSubst
            [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
    return (subst t1, subst t2, map subst qs)
consRelSynthApp _ _ RFun{} RFun{} ps d1@(Var _) d2@(Var _)
  = F.panic $ "consRelSynthApp: multiple rel sigs not supported " ++ F.showpp (ps, d1, d2)
consRelSynthApp _ _ RFun{} RFun{} _ d1 d2 =
  F.panic $ "consRelSynthApp: expected application to variables, got" ++ F.showpp (d1, d2)
consRelSynthApp _ _ t1 t2 p d1 d2 =
  F.panic $ "consRelSynthApp: malformed function types or predicate for arguments " ++ F.showpp (t1, t2, p, d1, d2)

--------------------------------------------------------------
-- Unary Rules -----------------------------------------------
--------------------------------------------------------------

symbolType :: CGEnv -> Var -> String -> SpecType
symbolType γ x msg
  | Just t <- γ ?= F.symbol x = t
  | otherwise = F.panic $ msg ++ " " ++ F.showpp x ++ " not in scope " ++ F.showpp γ

consUnarySynth :: CGEnv -> CoreExpr -> CG SpecType
consUnarySynth γ (Tick t e) = consUnarySynth (γ `setLocation` Sp.Tick t) e
consUnarySynth γ (Var x) = return $ traceWhenLoud ("SELFIFICATION " ++ F.showpp (x, removeAbsRef $ selfify t x)) removeAbsRef $ selfify t x
  where t = symbolType γ x "consUnarySynth (Var)"
consUnarySynth _ e@(Lit c) =
  traceUSyn "Lit" e $ do
  return $ removeAbsRef $ uRType $ literalFRefType c
consUnarySynth γ e@(Let _ _) =
  traceUSyn "Let" e $ do
  t   <- freshTyType (typeclass (getConfig γ)) LetE e $ Ghc.exprType e
  addW $ WfC γ t
  consUnaryCheck γ e t
  return $ removeAbsRef t
consUnarySynth γ e'@(App e d) =
  traceUSyn "App" e' $ do
  et <- consUnarySynth γ e
  consUnarySynthApp γ et d
consUnarySynth γ e'@(Lam α e) | Ghc.isTyVar α =
                             traceUSyn "LamTyp" e' $ do
  γ' <- γ `extendWithTyVar` α
  t' <- consUnarySynth γ' e
  return $ removeAbsRef $ RAllT (makeRTVar $ rTyVar α) t' mempty
consUnarySynth γ e@(Lam x d)  =
  traceUSyn "Lam" e $ do
  let Ghc.FunTy { ft_arg = s' } = checkFun e $ Ghc.exprType e
  s  <- freshTyType (typeclass (getConfig γ)) LamE (Var x) s'
  γ' <- γ += ("consUnarySynth (Lam)", F.symbol x, s)
  t  <- consUnarySynth γ' d
  addW $ WfC γ s
  return $ removeAbsRef $ RFun (F.symbol x) (mkRFInfo $ getConfig γ) s t mempty
consUnarySynth γ e@(Case _ _ _ alts) =
  traceUSyn "Case" e $ do
  t   <- freshTyType (typeclass (getConfig γ)) (caseKVKind alts) e $ Ghc.exprType e
  addW $ WfC γ t
  return $ removeAbsRef t
consUnarySynth _ e@(Cast _ _) = F.panic $ "consUnarySynth is undefined for Cast " ++ F.showpp e
consUnarySynth _ e@(Type _) = F.panic $ "consUnarySynth is undefined for Type " ++ F.showpp e
consUnarySynth _ e@(Coercion _) = F.panic $ "consUnarySynth is undefined for Coercion " ++ F.showpp e

caseKVKind :: [Alt Var] -> KVKind
caseKVKind [Ghc.Alt (DataAlt _) _ (Var _)] = ProjectE
caseKVKind cs                      = CaseE (length cs)

checkFun :: CoreExpr -> Type -> Type
checkFun _ t@Ghc.FunTy{} = t
checkFun e t = F.panic $ "FunTy was expected but got " ++ F.showpp t ++ "\t for expression" ++ F.showpp e

base :: SpecType -> Bool
base RApp{} = True
base RVar{} = True
base _      = False

selfifyExpr :: SpecType -> F.Expr -> Maybe SpecType
selfifyExpr (RFun v i s t r) f = (\t' -> RFun v i s t' r) <$> selfifyExpr t (F.EApp f (F.EVar v))
selfifyExpr t e | base t = Just $ t `strengthen` eq e
  where eq = uTop . F.exprReft
selfifyExpr _ _ = Nothing

selfify :: F.Symbolic a => SpecType -> a -> SpecType
selfify t x | base t = t `strengthen` eq x
  where eq = uTop . F.symbolReft . F.symbol
selfify t e | Just t' <- selfifyExpr t (F.EVar $ F.symbol e) = t'
selfify t _ = t

consUnarySynthApp :: CGEnv -> SpecType -> CoreExpr -> CG SpecType
consUnarySynthApp γ t (Tick y e) = do
  consUnarySynthApp (γ `setLocation` Sp.Tick y) t e
consUnarySynthApp γ (RFun x _ s t _) d@(Var y) = do
  consUnaryCheck γ d s
  return $ t `F.subst1` (x, F.EVar $ F.symbol y)
consUnarySynthApp γ (RAllT α t _) (Type s) = do
    s' <- trueTy (typeclass (getConfig γ)) s
    return $ subsTyVarMeet' (ty_var_value α, s') t
consUnarySynthApp _ RFun{} d =
  F.panic $ "consUnarySynthApp expected Var as a funciton arg, got " ++ F.showpp d
consUnarySynthApp γ t@(RAllP{}) e
  = consUnarySynthApp γ (removeAbsRef t) e

consUnarySynthApp _ ft d =
  F.panic $ "consUnarySynthApp malformed function type " ++ F.showpp ft ++
            " for argument " ++ F.showpp d

consUnaryCheck :: CGEnv -> CoreExpr -> SpecType -> CG ()
consUnaryCheck γ (Let (NonRec x d) e) t = do
  s <- consUnarySynth γ d
  γ' <- γ += ("consUnaryCheck Let", F.symbol x, s)
  consUnaryCheck γ' e t
consUnaryCheck γ e t = do
  s <- consUnarySynth γ e
  addC (SubC γ s t) ("consUnaryCheck (Synth): s = " ++ F.showpp s ++ " t = " ++ F.showpp t)

--------------------------------------------------------------
-- Rel. Predicate Subtyping  ---------------------------------
--------------------------------------------------------------

consRelSub :: CGEnv -> SpecType -> SpecType -> F.Expr -> F.Expr -> CG ()
consRelSub γ f1@(RFun g1 _ s1@RFun{} t1 _) f2@(RFun g2 _ s2@RFun{} t2 _)
             pr1@(F.PImp qr1@F.PImp{} p1)  pr2@(F.PImp qr2@F.PImp{} p2)
  = traceSub "hof" f1 f2 pr1 pr2 $ do
    consRelSub γ s1 s2 qr2 qr1
    γ' <- γ += ("consRelSub HOF", F.symbol g1, s1)
    γ'' <- γ' += ("consRelSub HOF", F.symbol g2, s2)
    let psubst = unapplyArg resL g1 <> unapplyArg resR g2
    consRelSub γ'' t1 t2 (psubst p1) (psubst p2)
consRelSub γ f1@(RFun g1 _ s1@RFun{} t1 _) f2@(RFun g2 _ s2@RFun{} t2 _)
             pr1@(F.PAnd [F.PImp qr1@F.PImp{} p1])            pr2@(F.PImp qr2@F.PImp{} p2)
  = traceSub "hof" f1 f2 pr1 pr2 $ do
    consRelSub γ s1 s2 qr2 qr1
    γ' <- γ += ("consRelSub HOF", F.symbol g1, s1)
    γ'' <- γ' += ("consRelSub HOF", F.symbol g2, s2)
    let psubst = unapplyArg resL g1 <> unapplyArg resR g2
    consRelSub γ'' t1 t2 (psubst p1) (psubst p2)
consRelSub γ f1@(RFun x1 _ s1 e1 _) f2 p1 p2 =
  traceSub "fun" f1 f2 p1 p2 $ do
    γ' <- γ += ("consRelSub RFun L", F.symbol x1, s1)
    let psubst = unapplyArg resL x1
    consRelSub γ' e1 f2 (psubst p1) (psubst p2)
consRelSub γ f1 f2@(RFun x2 _ s2 e2 _) p1 p2 =
  traceSub "fun" f1 f2 p1 p2 $ do
    γ' <- γ += ("consRelSub RFun R", F.symbol x2, s2)
    let psubst = unapplyArg resR x2
    consRelSub γ' f1 e2 (psubst p1) (psubst p2)
consRelSub γ t1 t2 p1 p2 | isBase t1 && isBase t2 =
  traceSub "base" t1 t2 p1 p2 $ do
    rl <- fresh
    rr <- fresh
    γ' <- γ += ("consRelSub Base L", rl, t1)
    γ'' <- γ' += ("consRelSub Base R", rr, t2)
    let cstr = F.subst (F.mkSubst [(resL, F.EVar rl), (resR, F.EVar rr)]) $ F.PImp p1 p2
    entl γ'' (traceWhenLoud ("consRelSub Base cstr " ++ F.showpp cstr) cstr) "consRelSub Base"
consRelSub _ t1@(RHole _) t2@(RHole _) _ _ = F.panic $ "consRelSub is undefined for RHole " ++ show (t1, t2)
consRelSub _ t1@(RExprArg _) t2@(RExprArg _) _ _ = F.panic $ "consRelSub is undefined for RExprArg " ++ show (t1, t2)
consRelSub _ t1@REx {} t2@REx {} _ _ = F.panic $ "consRelSub is undefined for REx " ++ show (t1, t2)
consRelSub _ t1@RAllE {} t2@RAllE {} _ _ = F.panic $ "consRelSub is undefined for RAllE " ++ show (t1, t2)
consRelSub _ t1@RRTy {} t2@RRTy {} _ _ = F.panic $ "consRelSub is undefined for RRTy " ++ show (t1, t2)
consRelSub _ t1@RAllP {} t2@RAllP {} _ _ = F.panic $ "consRelSub is undefined for RAllP " ++ show (t1, t2)
consRelSub _ t1@RAllT {} t2@RAllT {} _ _ = F.panic $ "consRelSub is undefined for RAllT " ++ show (t1, t2)
consRelSub _ t1@RImpF {} t2@RImpF {} _ _ = F.panic $ "consRelSub is undefined for RImpF " ++ show (t1, t2)
consRelSub _ t1 t2 _ _ =  F.panic $ "consRelSub is undefined for different types " ++ show (t1, t2)

--------------------------------------------------------------
-- Helper Definitions ----------------------------------------
--------------------------------------------------------------

isFuncPred :: F.Expr -> Bool
isFuncPred (F.PImp _ _) = True
isFuncPred _            = False

partitionArg :: Var -> Var -> SpecType -> SpecType -> F.Expr -> (PrEnv, [F.Expr])
partitionArg x1 x2 s1 s2 q = partitionArgs [x1] [x2] [s1] [s2] [q]

partitionArgs :: [Var] -> [Var] -> [SpecType] -> [SpecType] -> [F.Expr] -> (PrEnv, [F.Expr])
partitionArgs xs1 xs2 ts1 ts2 qs = (map toRel ho, map toUnary fo)
 where
  (ho, fo) = L.partition (isFuncPred . toUnary) (zip5 xs1 xs2 ts1 ts2 qs)
  toRel (f1, f2, t1, t2, q) =
    let (vs1, ts1') = vargs t1
    in  let (vs2, ts2') = vargs t2
        in  let bs1 = zip vs1 (fst . vargs <$> ts1')
            in  let bs2 = zip vs2 (fst . vargs <$> ts2')
                in  let rp = RelPred f1 f2 bs1 bs2 $ ERBasic q
                    in traceWhenLoud ("partitionArgs toRel: " ++ F.showpp (f1, f2, bs1, bs2, q)) rp
  toUnary (_, _, _, _, q) = q

unRAllT :: SpecType -> String -> (RTVU RTyCon RTyVar, SpecType, RReft)
unRAllT (RAllT α2 ft2 r2) _ = (α2, ft2, r2)
unRAllT t msg = F.panic $ msg ++ ": expected RAllT, got: " ++ F.showpp t

forgetRAllP :: PVU RTyCon RTyVar -> SpecType -> SpecType
forgetRAllP _ t = t

args :: CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Expr ->
  Maybe ([Var], [Var], [F.Symbol], [F.Symbol], [SpecType], [SpecType], [F.Expr])
args e1 e2 t1 t2 ps
  | xs1 <- xargs e1, xs2 <- xargs e2,
    (vs1, ts1) <- vargs t1, (vs2, ts2) <- vargs t2,
    qs  <- prems ps,
    all (length qs ==) [length xs1, length xs2, length vs1, length vs2, length ts1, length ts2]
  = Just (xs1, xs2, vs1, vs2, ts1, ts2, qs)
args e1 e2 t1 t2 ps = traceWhenLoud ("args guard" ++ F.showpp (xargs e1, xargs e2, vargs t1, vargs t2, prems ps)) Nothing

xargs :: CoreExpr -> [Var]
xargs (Tick _ e) = xargs e
xargs (Lam  x e) | Ghc.isTyVar x = xargs e
xargs (Lam  x e) = x : xargs e
xargs _          = []

xbody :: CoreExpr -> CoreExpr
xbody (Tick _ e) = xbody e
xbody (Lam  _ e) = xbody e
xbody e          = e

refts :: SpecType -> [RReft]
refts (RAllT _ t r ) = r : refts t
refts (RFun _ _ _ t r) = r : refts t
refts _              = []

vargs :: SpecType -> ([F.Symbol], [SpecType])
vargs (RAllT _ t _ ) = vargs t
vargs (RFun v _ s t _) = bimap (v :) (s :) $ vargs t
vargs _              = ([], [])

ret :: SpecType -> SpecType
ret (RAllT _ t _ ) = ret t
ret (RFun _ _ _ t _) = ret t
ret t              = t

prems :: F.Expr -> [F.Expr]
prems (F.PImp q p) = q : prems p
prems _            = []

concl :: F.Expr -> F.Expr
concl (F.PImp _ p) = concl p
concl p            = p

extendWithTyVar :: CGEnv -> TyVar -> CG CGEnv
extendWithTyVar γ a
  | isValKind (Ghc.tyVarKind a)
  = γ += ("extendWithTyVar", F.symbol a, kindToRType $ Ghc.tyVarKind a)
  | otherwise
  = return γ

matchFunArgs :: SpecType -> SpecType -> F.Symbol -> F.Expr
matchFunArgs (RAllT _ t1 _) t2 x = matchFunArgs t1 t2 x
matchFunArgs t1 (RAllT _ t2 _) x = matchFunArgs t1 t2 x
matchFunArgs (RFun x1 _ _ t1 _) (RFun x2 _ _ t2 _) x =
  if x == x1 then F.EVar x2 else matchFunArgs t1 t2 x
matchFunArgs t1 t2 x | isBase t1 && isBase t2 = F.EVar x
matchFunArgs t1 t2 _ = F.panic $ "matchFunArgs undefined for " ++ F.showpp (t1, t2)

entl :: CGEnv -> F.Expr -> String -> CG ()
entl γ p = addC (SubR γ OCons $ uReft (F.vv_, F.PIff (F.EVar F.vv_) p))

entlFunReft :: CGEnv -> RReft -> String -> CG ()
entlFunReft γ r msg = do
  entl γ (F.reftPred $ ur_reft r) $ "entlFunRefts " ++ msg

entlFunRefts :: CGEnv -> RReft -> RReft -> String -> CG ()
entlFunRefts γ r1 r2 msg = do
  entlFunReft γ r1 $ msg ++ " L"
  entlFunReft γ r2 $ msg ++ " R"

subRelCopies :: CoreExpr -> Var -> CoreExpr -> Var -> (CoreExpr, CoreExpr)
subRelCopies e1 x1 e2 x2 = (subVarAndTy x1 evar1 e1, subVarAndTy x2 evar2 e2)
  where (evar1, evar2) = mkRelCopies x1 x2

subVarAndTy :: Var -> Var -> CoreExpr -> CoreExpr
subVarAndTy x v = subTy (M.singleton x $ TyVarTy v) . sub (M.singleton x $ Var v)

mkRelCopies :: Var -> Var -> (Var, Var)
mkRelCopies x1 x2 = (mkCopyWithSuffix relSuffixL x1, mkCopyWithSuffix relSuffixR x2)

mkCopyWithName :: String -> Var -> Var
mkCopyWithName s v =
  Ghc.setVarName v $ Ghc.mkSystemName (Ghc.getUnique v) (Ghc.mkVarOcc s)

mkCopyWithSuffix :: String -> Var -> Var
mkCopyWithSuffix s v = mkCopyWithName (Ghc.getOccString v ++ s) v

lookupBind :: Var -> [CoreBind] -> CoreBind
lookupBind x bs = case lookup x (concatMap binds bs) of
  Nothing -> F.panic $ "Not found definition for " ++ show x
  Just e  -> e
 where
  binds b@(NonRec x' _) = [ (x', b) ]
  binds   (Rec bs'    ) = [ (x', Rec [(x',e)]) | (x',e) <- bs' ]

subUnarySig :: CGEnv -> Var -> SpecType -> CG ()
subUnarySig γ x tRel =
  forM_ mkargs $ \(rt, ut) -> addC (SubC γ ut rt) $ "subUnarySig tUn = " ++ F.showpp ut ++ " tRel = " ++ F.showpp rt
  where
    mkargs = zip (snd $ vargs tRel) (snd $ vargs tUn)
    tUn = symbolType γ x $ "subUnarySig " ++ F.showpp x

addPred :: CGEnv -> F.Expr -> CG CGEnv
addPred γ p = extendWithExprs γ [p]

addPreds :: CGEnv -> [F.Expr] -> CG CGEnv
addPreds = extendWithExprs

extendWithExprs :: CGEnv -> [F.Expr] -> CG CGEnv
extendWithExprs γ ps = do
  dummy <- fresh
  let reft = uReft (F.vv_, F.PAnd ps)
  γ += ("extend with predicate env", dummy, RVar (symbolRTyVar F.dummySymbol) reft)

unapplyArg :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
unapplyArg f y e = F.mapExpr sb e
  where
    sb :: F.Expr -> F.Expr
    sb (F.EApp (F.EVar r) (F.EVar x))
      | r == f && x == y = F.EVar r
    sb e' = e'

unapplyRelArgs :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
unapplyRelArgs x1 x2 = unapplyArg resL x1 . unapplyArg resR x2

unapplyRelArgsR :: F.Symbol -> F.Symbol -> RelExpr -> RelExpr
unapplyRelArgsR x1 x2 (ERBasic e) = ERBasic (unapplyRelArgs x1 x2 e)
unapplyRelArgsR x1 x2 (ERChecked e re) = ERChecked (unapplyRelArgs x1 x2 e) (unapplyRelArgsR x1 x2 re)
unapplyRelArgsR x1 x2 (ERUnChecked e re) = ERUnChecked (unapplyRelArgs x1 x2 e) (unapplyRelArgsR x1 x2 re)

--------------------------------------------------------------
-- RelExpr & F.Expr ------------------------------------------
--------------------------------------------------------------

fromRelExpr :: RelExpr -> F.Expr
fromRelExpr (ERBasic e) = e
fromRelExpr (ERChecked a b) = F.PImp a (fromRelExpr b)
fromRelExpr (ERUnChecked a b) = F.PImp a (fromRelExpr b)

--------------------------------------------------------------
-- Debug -----------------------------------------------------
--------------------------------------------------------------


traceSub :: (PPrint t, PPrint s, PPrint p, PPrint q) => String -> t -> s -> p -> q -> a -> a
traceSub msg t s p q = traceWhenLoud (msg ++ " RelSub\n"
                      ++ "t: " ++ F.showpp t ++ "\n\n"
                      ++ "s: " ++ F.showpp s ++ "\n\n"
                      ++ "p: " ++ F.showpp p ++ "\n\n"
                      ++ "q: " ++ F.showpp q)


traceChk
  :: (PPrint e, PPrint d, PPrint t, PPrint s, PPrint p)
  => String -> e -> d -> t -> s -> p -> a -> a
traceChk expr = trace (expr ++ " To CHECK")

traceSyn
  :: (PPrint e, PPrint d, PPrint a, PPrint b, PPrint c)
  => String -> e -> d -> CG (a, b, c) -> CG (a, b, c)
traceSyn expr e d cg
  = do
    (a, b, c) <- cg
    trace (expr ++ " To SYNTH") e d a b c cg

traceSynApp
  :: (PPrint e, PPrint d, PPrint a, PPrint b, PPrint c)
  => e -> d -> a -> b -> c -> t -> t
traceSynApp = trace "SYNTH APP TO "

traceUSyn
  :: (PPrint e, PPrint a)
  => String -> e -> CG a -> CG a
traceUSyn expr e cg = do
  t <- cg
  trace (expr ++ " To SYNTH UNARY") e dummy t dummy dummy cg
  where dummy = F.PTrue

trace
  :: (PPrint e, PPrint d, PPrint t, PPrint s, PPrint p)
  => String -> e -> d -> t -> s -> p -> a -> a
trace msg e d t s p = traceWhenLoud (msg ++ "\n"
                      ++ "e: " ++ F.showpp e ++ "\n\n"
                      ++ "d: " ++ F.showpp d ++ "\n\n"
                      ++ "t: " ++ F.showpp t ++ "\n\n"
                      ++ "s: " ++ F.showpp s ++ "\n\n"
                      ++ "p: " ++ F.showpp p)

traceWhenLoud :: String -> a -> a
traceWhenLoud s a = unsafePerformIO $ whenLoud (putStrLn s) >> return a
