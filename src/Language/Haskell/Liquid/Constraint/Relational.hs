{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE ScopedTypeVariables        #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Relational (consAssmRel, consRelTop) where


#if !MIN_VERSION_base(4,14,0)
import           Control.Monad.Fail
#endif


import           Control.Monad.State
import           Data.Bifunctor                as B
import qualified Data.HashMap.Strict           as M
import qualified Data.List                     as L
import           Data.List.Split               as L
import           Data.Monoid                    ( Any(..) )
import           Data.String                    ( IsString(..) )
import           Data.Char                      ( toUpper )
import           Data.Default                   ( def )
-- import qualified Debug.Trace                                    as D
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Types.Visitor
                                               as F
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Synthesize.GHC
                                                ( coreToHs
                                                , fromAnf
                                                )

import           Liquid.GHC.API                 ( Alt
                                                , AltCon(..)
                                                , Bind(..)
                                                , CoreBind
                                                , CoreBndr
                                                , CoreExpr
                                                , Expr(..)
                                                , Type(..)
                                                , TyVar
                                                , Var(..)
                                                )
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

import           Text.PrettyPrint.HughesPJ (text
                                           , Doc
                                           , ($+$)
                                           , Mode(..)
                                           , Style(..)
                                           , TextDetails(..)
                                           , fullRender)

data RelPred
  = RelPred { fun1 :: Var
            , fun2 :: Var
            , args1 :: [(F.Symbol, [F.Symbol])]
            , args2 :: [(F.Symbol, [F.Symbol])]
            , prop :: RelExpr
            } deriving Show

type RelEnv = [RelPred]

type UnaryChecking = CGEnv -> CoreExpr -> SpecType -> CG ()
type UnarySynthesis = CGEnv -> CoreExpr -> CG SpecType
data UnaryTyping = UnaryTyping { chk :: UnaryChecking
                               , syn :: UnarySynthesis
                               }

consAssmRel :: Config -> TargetInfo -> (RelEnv, CGEnv) -> (Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr) -> CG (RelEnv, CGEnv)
consAssmRel _ _ (ψ, γ) (x, y, t, s, ra, rp) = do
  modify $ \cgi -> cgi { relWf = errs ++ relWf cgi }
  if not (null errs) 
    then return (ψ, γ) 
    else traceChk "Assm" x y t s p $ do
      traceWhenLoud ("ASSUME " ++ F.showpp (fromRelExpr p', p)) $ subUnarySig γ' x t'
      subUnarySig γ' y s'
      γ'' <- if isBasicType t' && isBasicType s'
        then γ' `addPred` F.subst
          (F.mkSubst [(resL, F.EVar $ F.symbol x), (resR, F.EVar $ F.symbol y)])
          (fromRelExpr rp)
        else return γ'
      return (RelPred x' y' bs cs rp : ψ, γ'')
 where
    errs = wfErrors (F.loc t) x y t' s' ra rp
    p = fromRelExpr rp
    γ' = γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc t))
    (x', y') = mkRelCopies x y
    t' = removeAbsRef $ val t
    s' = removeAbsRef $ val s
    (vs, ts) = vargs t'
    (us, ss) = vargs s'
    bs = zip vs (fst . vargs <$> ts)
    cs = zip us (fst . vargs <$> ss)
    p' = L.foldl (\q (v, u) -> unapplyRelArgsR v u q) rp (zip vs us)

consRelTop :: Config -> TargetInfo -> UnaryChecking -> UnarySynthesis -> CGEnv -> RelEnv -> (Var, Var, LocSpecType, LocSpecType, RelExpr, RelExpr) -> CG ()
consRelTop cfg ti chk _ γ ψ (x, y, t, s, ra, rp) = traceChk "Init" e d t s p $ do
    subUnarySig γ' x t'
    subUnarySig γ' y s'
    consRelCheckBind (UnaryTyping chk consUnarySynth) γ' ψ e d t' s' ra rp
    when (relationalHints cfg) $ 
      modify $ \cgi -> cgi
      { relHints = relHint
                      (relSigToUnSig (toExpr x) (toExpr y) t' s' rp)
                      hintName
                      (relTermToUnTerm x y hintName (toCoreExpr e) (toCoreExpr d))
                    $+$ relHints cgi
      }
  where
    toExpr = F.EVar . F.symbol
    toCoreExpr = GM.unTickExpr . binderToExpr
    p = fromRelExpr rp
    γ' = γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc t))
    cbs = giCbs $ giSrc ti
    e = lookupBind x cbs
    d = lookupBind y cbs
    t' = removeAbsRef $ val t
    s' = removeAbsRef $ val s
    hintName = mkRelThmVar x y

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
-- Rel to Unary Translation ----------------------------------
--------------------------------------------------------------

relSigToUnSig :: F.Expr -> F.Expr -> SpecType -> SpecType -> RelExpr -> SpecType
{- relSigToUnSig :: EVar -> EVar -> t1:SpecType -> t2:SpecType -> p:RelExpr -> t:SpecType
      translates rel type {t1 ~ t2 | p} to unary t

   FIRST-ORDER types:
  
    relational incr ~ incr :: { (x1:Int) -> Int 
                              ~ (x2:Int) -> Int
                              | x1 < x2 => r1 x1 < r2 x2 }

              translates to:
                      
    relIncrIncr :: x1:Int -> {x2:Int | x1 < x2} -> {incr x1 < incr x2} 


   HIGHER-ORDER types:

   relational any ~ any :: { p1:(x1:Int -> Bool) -> xs1:[Int] -> Bool
                           ~ p2:(x2:Int -> Bool) -> xs2:[Int] -> Bool
                           | (x1 = x2 => (r1 x1 => r2 x2)) && p1 == p2  !=> xs1 = xs2 => (r1 p1 xs1 => r2 p2 xs2)}

              translates to:
                      
   relAnyAny :: p1:(x1:Int -> Bool) -> p2:(x2:Int -> Bool) 
             -> relP1P2: (x1:Int -> {x2:Int|x1 = x2} -> {p1 x1 => p2 x2})
             -> xs1:[Int] -> xs2:[Int]
             -> {relXs1Xs2:()|xs1 = xs2}
             -> {any p1 xs1 => any p2 xs2} 

  map p1 = map p2 ????
  
  TODO: How to handle funciton equality?

  E.g.:
   
   relational any ~ any :: { p1:(x1:Int -> Bool) -> xs1:[Int] -> Bool
                           ~ p2:(x2:Int -> Bool) -> xs2:[Int] -> Bool
                           | p1 = p2 => xs1 = xs2 => r1 p1 xs1 => r2 p2 xs2}

  p1 = p2 => map p1 = map p2 -- we get it for free

 -}

-- Higher-Order Case. Argument types are functons && checking mode is on:
relSigToUnSig e1 e2 (RFun x1 i1 s1@RFun{} t1 r1) (RFun x2 i2 s2@RFun{} t2 r2) (ERChecked q p)
  = traceWhenLoud "relSigToUnSig RFun RFun ERChecked" $ 
      RFun x1 i1 s1 
        (RFun x2 i2 s2 
                            -- TODO: how to get i?    
          (RFun (mkRelLemma x1 x2) i2 (relSigToUnSig (F.EVar x1) (F.EVar x2) s1 s2 q) (relSigToUnSig e1 e2 t1 t2 p) r2) r2) r1 
-- First-Order Cases:
relSigToUnSig e1 e2 (RFun x1 i1 s1 t1 r1) (RFun x2 i2 s2 t2 r2) (ERUnChecked q p)
  = traceWhenLoud "relSigToUnSig RFun RFun ERUnChecked" $ 
    RFun x1 i1 s1 (RFun x2 i2 (s2 `strengthen` exprToUReft q) (relSigToUnSig e1 e2 t1 t2 p) r2) r1
relSigToUnSig e1 e2 (RFun x1 i1 s1 t1 r1) (RFun x2 i2 s2 t2 r2) (ERChecked q p)
  = traceWhenLoud "relSigToUnSig RFun RFun ERChecked" $ 
    RFun x1 i1 s1 (RFun x2 i2 (s2 `strengthen` exprToUReft (fromRelExpr q)) (relSigToUnSig e1 e2 t1 t2 p) r2) r1
relSigToUnSig _ _ RFun{} RFun{} p@ERBasic{}
  = traceWhenLoud "relSigToUnSig RFun RFun ERBasic" $ 
    F.panic $ "relSigToUnSig: predicate " ++ F.showpp p ++ " too short for function types"
relSigToUnSig _ _ t1@RFun{} t2 p
  = F.panic $ "relSigToUnSig: unsuppoted pair of types RFun and non-RFun " ++ F.showpp (t1, t2, p) 
relSigToUnSig _ _ t1 t2@RFun{} p
  = F.panic $ "relSigToUnSig: unsuppoted pair of types non-RFun and RFun " ++ F.showpp (t1, t2, p) 
relSigToUnSig e1 e2 t1 t2 (ERBasic p) | isBasicType t1 && isBasicType t2
  = traceWhenLoud "relSigToUnSig Base Base ERBasic" $ 
    unitTy `strengthen` uReft (F.vv_, rs2es (F.PAnd [p]))
    where 
      rs2es =  F.subst $ F.mkSubst [(resL, e1), (resR, e2)]
      unitTy = RApp (RTyCon Ghc.unitTyCon [] def) [] [] mempty
relSigToUnSig _ _ t1 t2 p | isBasicType t1 && isBasicType t2
  = F.panic $ "relSigToUnSig: predicate " ++ F.showpp p ++ " too long for basic types"
relSigToUnSig _ _ t1 t2 p 
  = F.panic $ "relSigToUnSig: unsuppoted pair of types " ++ F.showpp (t1, t2, p)

isBasicType :: SpecType -> Bool
isBasicType RVar{}   = True
isBasicType t@RApp{} = isBase t
isBasicType _        = False

mkRelLemma :: F.Symbol -> F.Symbol -> F.Symbol
mkRelLemma s1 s2 = F.symbol $ "lemma" ++ cap (F.symbolString s1) ++ cap (F.symbolString s2)

mkRelThmVar :: Var -> Var -> Var
mkRelThmVar x y = mkCopyWithName ("rel" ++ cap (trimModuleName $ show x) ++ cap (trimModuleName $ show y)) x
  where
    trimModuleName = last . L.splitOn "."

cap :: String -> String
cap (c:cs) = toUpper c : cs
cap cs = cs

relTermToUnTerm :: Var -> Var -> Var -> CoreExpr -> CoreExpr -> CoreExpr
relTermToUnTerm e1 e2 relThm = relTermToUnTerm' [((e1, e2), Var relThm)]

relTermToUnTerm' :: [((Var, Var), CoreExpr)] -> CoreExpr -> CoreExpr -> CoreExpr
relTermToUnTerm' relTerms (Var x1) (Var x2)
  | Just relX <- lookup (x1, x2) relTerms 
  = relX
relTermToUnTerm' relTerms (App f1 α1) (App f2 α2) 
  | Type{} <- GM.unTickExpr α1, Type{} <- GM.unTickExpr α2 
  = relTermToUnTerm' relTerms f1 f2
relTermToUnTerm' relTerms (App f1 (Var x1)) (App f2 (Var x2)) 
  | GM.isEmbeddedDictVar x1, GM.isEmbeddedDictVar x2
  = relTermToUnTerm' relTerms f1 f2
relTermToUnTerm' relTerms (App f1 x1) (App f2 x2) 
  | isCommonArg x1, isCommonArg x2
  = App (App (relTermToUnTerm' relTerms f1 f2) x1) x2
  where 
    isCommonArg x | Type{} <- GM.unTickExpr x = False
    isCommonArg x | Var v <- GM.unTickExpr x = not (GM.isEmbeddedDictVar v)
    isCommonArg _ = True
relTermToUnTerm' relTerms (Lam α1 e1) (Lam α2 e2) 
  | Ghc.isTyVar α1, Ghc.isTyVar α2
  = relTermToUnTerm' relTerms e1 e2
relTermToUnTerm' relTerms (Lam x1 e1) (Lam x2 e2)
  | not (Ghc.isTyVar x1), not (Ghc.isTyVar x2)
  = Lam x1l $ Lam x2r $ relTermToUnTerm' relTerms e1l e2r
  where
    (x1l, x2r) = mkRelCopies x1 x2
    (e1l, e2r) = subRelCopies e1 x1 e2 x2
relTermToUnTerm' relTerms (Let (NonRec x1 d1) e1) (Let (NonRec x2 d2) e2) 
  = Let (NonRec x1l d1) $ Let (NonRec x2r d2) $ Let (NonRec relX relD) $ relTermToUnTerm' (((x1l, x2r), Var relX) : relTerms) e1l e2r
    where 
      relX = mkRelThmVar x1 x2
      relD = relTermToUnTerm' relTerms d1 d2
      (x1l, x2r) = mkRelCopies x1 x2
      (e1l, e2r) = subRelCopies e1 x1 e2 x2
-- TODO: test recursive and mutually recursive lets
relTermToUnTerm' relTerms (Let (Rec bs1) e1) (Let (Rec bs2) e2) 
  | length bs1 == length bs2 
  = Let (Rec bs1l) $ Let (Rec bs2r) $ Let (Rec relBs) $ relTermToUnTerm' relTerms' e1l e2r
    where 
      bs1l = mkLeftCopies bs1
      bs2r = mkRightCopies bs2
      e1l  = subOneSideCopies e1 bs1 bs1l
      e2r  = subOneSideCopies e2 bs2 bs2r
      relTermsBs = zipWith (\(x1, d1) (x2, d2) -> ((x1, x2), relTermToUnTerm' relTerms d1 d2)) bs1 bs2
      relTerms' = relTermsBs ++ relTerms
      relBs = zipWith (\(x1, d1) (x2, d2) -> (mkRelThmVar x1 x2, relTermToUnTerm' relTerms' d1 d2)) bs1 bs2
relTermToUnTerm' relTerms (Case d1 x1 t1 as1) (Case d2 x2 t2 as2) 
  = Case d1 x1l t1 $ map
    (\(c1, bs1, e1) ->
      let bs1l = map (mkCopyWithSuffix relSuffixL) bs1 in
      ( c1
      , bs1l
      , Case d2 x2r t2 $ map
        (\(c2, bs2, e2) ->
          let bs2r = map (mkCopyWithSuffix relSuffixR) bs2
              e1l  = subVarAndTys ((x1, x1l) : zip bs1 bs1l) e1
              e2r  = subVarAndTys ((x2, x2r) : zip bs2 bs2r) e2 
          in  (c2, bs2r, relTermToUnTerm' relTerms e1l e2r)
        )
        as2
      ))
    as1
    where (x1l, x2r) = mkRelCopies x1 x2
relTermToUnTerm' _ e1 e2
  = traceWhenLoud ("relTermToUnTerm': can't proceed proof generation on e1:\n" ++ F.showpp e1 ++ "\ne2:\n" ++ F.showpp e2)
      mkLambdaUnit (Ghc.exprType e1) (Ghc.exprType e2)
      
mkLambdaUnit :: Type -> Type -> CoreExpr
mkLambdaUnit (Ghc.ForAllTy _ t1) t2 = mkLambdaUnit t1 t2
mkLambdaUnit t1 (Ghc.ForAllTy _ t2) = mkLambdaUnit t1 t2
mkLambdaUnit (Ghc.FunTy Ghc.InvisArg _ _ t1) (Ghc.FunTy Ghc.InvisArg _ _ t2) = mkLambdaUnit t1 t2
mkLambdaUnit (Ghc.FunTy Ghc.VisArg _ _ t1) (Ghc.FunTy Ghc.VisArg _ _ t2) = Lam (GM.stringVar "_" Ghc.unitTy) $ Lam (GM.stringVar "_" Ghc.unitTy) $ mkLambdaUnit t1 t2
mkLambdaUnit t1@Ghc.FunTy{} t2 = F.panic $ "relTermToUnTerm: asked to relate unmatching types " ++ F.showpp t1 ++ " " ++ F.showpp t2
mkLambdaUnit t1 t2@Ghc.FunTy{} = F.panic $ "relTermToUnTerm: asked to relate unmatching types " ++ F.showpp t1 ++ " " ++ F.showpp t2
mkLambdaUnit _ _ = Ghc.unitExpr

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

resL, resR :: F.Symbol
resL = fromString "r1"
resR = fromString "r2"

relSuffixL, relSuffixR :: String
relSuffixL = "l"
relSuffixR = "r"

isSupported :: SpecType -> Bool
isSupported t | isBasicType t = True
isSupported RAllT{} = True
isSupported RFun{} = True
isSupported _ = False

wfErrors :: F.SourcePos -> Var -> Var -> SpecType -> SpecType -> RelExpr -> RelExpr -> [Error]
wfErrors loc e1 e2 t1 t2 _ p | not (isSupported t1) = [relWfError loc e1 e2 t1 t2 p "unsupported left type"]
wfErrors loc e1 e2 t1 t2 _ p | not (isSupported t2) = [relWfError loc e1 e2 t1 t2 p "unsupported right type"]
wfErrors loc e1 e2 (RAllT _ t1 _) t2 a p = wfErrors loc e1 e2 t1 t2 a p
wfErrors loc e1 e2 t1 (RAllT _ t2 _) a p = wfErrors loc e1 e2 t1 t2 a p
wfErrors _ _ _ t1 t2 _ (ERBasic _) | isBasicType t1 && isBasicType t2 = []
wfErrors loc e1 e2 (RFun _ _ _ t1 _) (RFun _ _ _ t2 _) a (ERUnChecked _ p) = wfErrors loc e1 e2 t1 t2 a p
wfErrors loc e1 e2 (RFun _ _ s1 t1 _) (RFun _ _ s2 t2 _) a (ERChecked q p) 
  = wfErrors loc e1 e2 s1 s2 a q ++ wfErrors loc e1 e2 t1 t2 a p
wfErrors loc e1 e2 t1@RFun{} t2@RFun{} _ p = [relWfError loc e1 e2 t1 t2 p "unexpected base predicate for function types"]
wfErrors loc e1 e2 t1 t2 _ p = [relWfError loc e1 e2 t1 t2 p "function type compared against base type"]

consRelCheckBind :: UnaryTyping -> CGEnv -> RelEnv -> CoreBind -> CoreBind -> SpecType -> SpecType -> RelExpr -> RelExpr -> CG ()
consRelCheckBind unary γ ψ b1@(NonRec _ e1) b2@(NonRec _ e2) t1 t2 ra rp
  = traceChk "Bind NonRec" b1 b2 t1 t2 p $ do
    γ' <- γ `addPred` a
    consRelCheck unary γ' ψ e1 e2 t1 t2 p
  where
    a = fromRelExpr ra
    p = fromRelExpr rp

consRelCheckBind unary γ ψ b1@NonRec{} (Rec [(x2, e2)]) t1 t2 a p =
  consRelCheckBind unary γ ψ b1 (NonRec x2 e2) t1 t2 a p

consRelCheckBind unary γ ψ (Rec [(x1, e1)]) b2@NonRec{} t1 t2 a p =
  consRelCheckBind unary γ ψ (NonRec x1 e1) b2 t1 t2 a p

consRelCheckBind unary γ ψ b1@(Rec [(f1, e1)]) b2@(Rec [(f2, e2)]) t1 t2 ra rp
  | Just (xs1, xs2, vs1, vs2, ts1, ts2, qs) <- args e1 e2 t1 t2 p
  = traceChk "Bind Rec" b1 b2 t1 t2 p $ do
    forM_ (refts t1 ++ refts t2) (\r -> entlFunReft γ r "consRelCheckBind Rec")
    let xs1l = map (mkCopyWithSuffix relSuffixL) xs1
    let xs2r = map (mkCopyWithSuffix relSuffixR) xs2
    let e1' = subVarAndTys ((f1, f1l) : zip xs1 xs1l) e1
    let e2' = subVarAndTys ((f2, f2r) : zip xs2 xs2r) e2
    γ' <- γ += ("Bind Rec f1", F.symbol f1l, t1) >>= (+= ("Bind Rec f2", F.symbol f2r, t2))
    γ'' <- foldM (\γγ (x, t) -> γγ += ("Bind Rec x1", F.symbol x, t)) γ' (zip (xs1l ++ xs2r) (ts1 ++ ts2))
    let vs2xs =  F.subst $ F.mkSubst $ zip (vs1 ++ vs2) $ map (F.EVar . F.symbol) (xs1l ++ xs2r)
    let (ho, fo) = partitionArgs xs1 xs2 ts1 ts2 qs
    γ''' <- γ'' `addPreds` traceWhenLoud ("PRECONDITION " ++ F.showpp (vs2xs (F.PAnd fo)) ++ "\n" ++
                                          "ASSUMPTION " ++ F.showpp (vs2xs a))
                              map vs2xs [F.PAnd fo, a]
    let p' = unapp rp (zip vs1 vs2)
    let ψ' = ho ++ ψ
    consRelCheck unary γ''' ψ' (xbody e1') (xbody e2') (vs2xs $ ret t1) (vs2xs $ ret t2) (vs2xs $ concl (fromRelExpr p'))
  where
    a = fromRelExpr ra
    p = fromRelExpr rp
    (f1l, f2r) = mkRelCopies f1 f2
    unapp :: RelExpr -> [(F.Symbol, F.Symbol)] -> RelExpr
    unapp = L.foldl' (\p' (v1, v2) -> unapplyRelArgsR v1 v2 p')

consRelCheckBind _ _ _ (Rec [(_, e1)]) (Rec [(_, e2)]) t1 t2 _ rp
  = F.panic $ "consRelCheckBind Rec: exprs, types, and pred should have same number of args " ++
    show (args e1 e2 t1 t2 p)
    where
      p = fromRelExpr rp

consRelCheckBind _ _ _ b1 b2 _ _ _ _
  = F.panic $ "consRelCheckBind Rec: mutually recursive binders are not supported " ++ F.showpp (b1, b2)

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelCheck :: UnaryTyping -> CGEnv -> RelEnv -> CoreExpr -> CoreExpr ->
  SpecType -> SpecType -> F.Expr -> CG ()
consRelCheck unary γ ψ (Tick tt e) d t s p =
  {- traceChk "Left Tick" e d t s p $ -} consRelCheck unary (γ `setLocation` Sp.Tick tt) ψ e d t s p

consRelCheck unary γ ψ e (Tick tt d) t s p =
  {- traceChk "Right Tick" e d t s p $ -} consRelCheck unary (γ `setLocation` Sp.Tick tt) ψ e d t s p

consRelCheck unary γ ψ l1@(Lam α1 e1) e2 rt1@(RAllT s1 t1 r1) t2 p
  | Ghc.isTyVar α1
  = traceChk "Lam Type L" l1 e2 rt1 t2 p $ do
    entlFunReft γ r1 "consRelCheck Lam Type"
    γ'  <- γ `extendWithTyVar` α1
    consRelCheck unary γ' ψ e1 e2 (sb (s1, α1) t1) t2 p
  where sb (s, α) = subsTyVarMeet' (ty_var_value s, rVar α)

consRelCheck unary γ ψ e1 l2@(Lam α2 e2) t1 rt2@(RAllT s2 t2 r2) p
  | Ghc.isTyVar α2
  = traceChk "Lam Type" e1 l2 t1 rt2 p $ do
    entlFunReft γ r2 "consRelCheck Lam Type"
    γ'  <- γ `extendWithTyVar` α2
    consRelCheck unary γ' ψ e1 e2 t1 (sb (s2, α2) t2) p
  where sb (s, α) = subsTyVarMeet' (ty_var_value s, rVar α)

consRelCheck unary γ ψ l1@(Lam x1 e1) l2@(Lam x2 e2) rt1@(RFun v1 _ s1 t1 r1) rt2@(RFun v2 _ s2 t2 r2) pr@(F.PImp q p)
  = traceChk "Lam Expr" l1 l2 rt1 rt2 pr $ do
    entlFunRefts γ r1 r2 "consRelCheck Lam Expr"
    let (pvar1, pvar2) = (F.symbol evar1, F.symbol evar2)
    let subst = F.subst $ F.mkSubst [(v1, F.EVar pvar1), (v2, F.EVar pvar2)]
    γ'  <- γ += ("consRelCheck Lam L", pvar1, subst s1)
    γ'' <- γ' += ("consRelCheck Lam R", pvar2, subst s2)
    let p'    = unapplyRelArgs v1 v2 p
    let (ho, fo) = partitionArg x1 x2 s1 s2 q
    γ''' <- γ'' `addPreds` traceWhenLoud ("PRECONDITION " ++ F.showpp (map subst fo)) map subst fo
    consRelCheck unary γ''' (ho ++ ψ) e1' e2' (subst t1) (subst t2) (subst p')
  where
    (evar1, evar2) = mkRelCopies x1 x2
    (e1', e2')     = subRelCopies e1 x1 e2 x2

consRelCheck unary γ ψ l1@(Let (NonRec x1 d1) e1) l2@(Let (NonRec x2 d2) e2) t1 t2 p
  = traceChk "Let" l1 l2 t1 t2 p $ do
    (s1, s2, qs) <- consRelSynth unary γ ψ d1 d2
    let q = head $ qs ++ [F.PTrue]
    let (evar1, evar2) = mkRelCopies x1 x2
    let (e1', e2')     = subRelCopies e1 x1 e2 x2
    γ'  <- γ += ("consRelCheck Let L", F.symbol evar1, s1)
    γ'' <- γ' += ("consRelCheck Let R", F.symbol evar2, s2)
    let rs2xs = F.mkSubst [(resL, F.EVar $ F.symbol evar1), (resR, F.EVar $ F.symbol evar2)]
    let (vs1, ts1) = vargs s1
    let (vs2, ts2) = vargs s2
    let binders = vs1 ++ vs2 ++ concatMap (fst . vargs) ts1 ++ concatMap (fst . vargs) ts2
    let q' = traceWhenLoud ("Let q: " ++ F.showpp q) q
    let (ho, fo) = L.partition (containsVars binders) [q']
    γ''' <- γ'' `addPreds` map (F.subst rs2xs) fo
    let ψ' = ψ ++ map (\qq -> toRel (evar1, evar2, s1, s2, qq)) ho
    consRelCheck unary γ''' ψ' e1' e2' t1 t2 p
  where 
    -- unapp    = L.foldl' (\p (v1, v2) -> unapplyRelArgs v1 v2 p)
    toRel (f1, f2, t1', t2', q) =
      let (vs1, ts1) = vargs t1'
      in  let (vs2, ts2) = vargs t2'
          in  let bs1 = zip vs1 (fst . vargs <$> ts1)
              in  let bs2 = zip vs2 (fst . vargs <$> ts2)
                  -- TODO: add symmetric RelPred
                  in  let rp = RelPred f1 f2 bs1 bs2 $ ERBasic q
                      in traceWhenLoud ("consRelCheck toRel: " ++ F.showpp (f1, f2, bs1, bs2, q)) rp
  

consRelCheck unary γ ψ l1@(Let (Rec []) e1) l2@(Let (Rec []) e2) t1 t2 p
  = traceChk "Let Rec Nil" l1 l2 t1 t2 p $ do
    consRelCheck unary γ ψ e1 e2 t1 t2 p

consRelCheck unary γ ψ l1@(Let (Rec ((x1, d1):bs1)) e1) l2@(Let (Rec ((x2, d2):bs2)) e2) t1 t2 p
  = traceChk "Let Rec Cons" l1 l2 t1 t2 p $ do
    (s1, s2, qs) <- consRelSynth unary γ ψ d1 d2
    let q = head $ qs ++ [F.PTrue]
    let (evar1, evar2) = mkRelCopies x1 x2
    let (e1', e2')     = subRelCopies e1 x1 e2 x2
    γ'  <- γ += ("consRelCheck Let L", F.symbol evar1, s1)
    γ'' <- γ' += ("consRelCheck Let R", F.symbol evar2, s2)
    let rs2xs = F.mkSubst [(resL, F.EVar $ F.symbol evar1), (resR, F.EVar $ F.symbol evar2)]
    let (vs1, ts1) = vargs s1
    let (vs2, ts2) = vargs s2
    let binders = vs1 ++ vs2 ++ concatMap (fst . vargs) ts1 ++ concatMap (fst . vargs) ts2
    γ''' <- γ'' `addPreds` map (F.subst rs2xs) (filter (not . containsVars binders) [q])
    consRelCheck unary γ''' ψ (Let (Rec bs1) e1') (Let (Rec bs2) e2') t1 t2 p

{- consRelCheck γ ψ c1@(Case e1 x1 _ alts1) c2@(Case e2 x2 _ alts2) t1 t2 p 
  | Just alts <- unifyAlts x1 x2 alts1 alts2 = 
  traceChk "Case Sync " c1 c2 t1 t2 p $ do
  (s1, s2, _) <- consRelSynth γ ψ e1 e2
  γ' <- γ += ("consRelCheck Case Sync L", x1', s1)
  γ'' <- γ' += ("consRelCheck Case Sync R", x2', s2)
  forM_ (ctors alts) $ consSameCtors γ'' ψ x1' x2' s1 s2 (nonDefaults alts)
  forM_ alts $ consRelCheckAltSync γ'' ψ t1 t2 p x1' x2' s1 s2
  where
    nonDefaults = filter (/= DEFAULT) . ctors
    ctors = map (\(c, _, _, _, _) -> c)
    (evar1, evar2) = mkRelCopies x1 x2
    x1' = F.symbol evar1
    x2' = F.symbol evar2 -}

consRelCheck unary γ ψ c1@(Case e1 x1 _ alts1) e2 t1 t2 p =
  traceChk "Case Async L" c1 e2 t1 t2 p $ do
    s1 <- syn unary γ e1
    γ' <- γ += ("consRelCheck Case Async L", F.symbol x1', s1)
    forM_ alts1 $ consRelCheckAltAsyncL unary γ' ψ t1 t2 p x1 x1' s1 e2
  where
    x1' = mkCopyWithSuffix relSuffixL x1

consRelCheck unary γ ψ e1 c2@(Case e2 x2 _ alts2) t1 t2 p =
  traceChk "Case Async R" e1 c2 t1 t2 p $ do
    s2 <- syn unary γ e2
    γ' <- γ += ("consRelCheck Case Async R", F.symbol x2', s2)
    forM_ alts2 $ consRelCheckAltAsyncR unary γ' ψ t1 t2 p e1 x2 x2' s2
  where
    -- TODO: where is subRelCopies?
    x2' = mkCopyWithSuffix relSuffixR x2

consRelCheck unary γ ψ e d t1 t2 p =
  traceChk "Synth" e d t1 t2 p $ do
  (s1, s2, qs) <- consRelSynth unary γ ψ e d
  let psubst = F.substf (matchFunArgs t1 s1) . F.substf (matchFunArgs t2 s2)
  consRelSub γ s1 s2 (F.PAnd qs) (psubst p)
  addC (SubC γ s1 t1) ("consRelCheck (Synth): s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γ s2 t2) ("consRelCheck (Synth): s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)

-- consSameCtors :: CGEnv -> RelEnv -> F.Symbol -> F.Symbol -> SpecType -> SpecType -> [AltCon] -> AltCon  -> CG ()
-- consSameCtors γ _ x1 x2 _ _ _ (DataAlt c) | isBoolDataCon c
--   = entl γ (F.PIff (F.EVar x1) (F.EVar x2)) "consSameCtors DataAlt Bool"
-- consSameCtors γ _ x1 x2 _ _ _ (DataAlt c)
--   = entl γ (F.PIff (isCtor c $ F.EVar x1) (isCtor c $ F.EVar x2)) "consSameCtors DataAlt"
-- consSameCtors _ _ _ _ _ _ _ (LitAlt _)
--   = F.panic "consSameCtors undefined for literals"
-- consSameCtors _ _ _ _ _ _ _ DEFAULT
--   = F.panic "consSameCtors undefined for default"

consExtAltEnv :: CGEnv -> F.Symbol -> SpecType -> AltCon -> [Var] -> CoreExpr -> String -> CG (CGEnv, CoreExpr)
consExtAltEnv γ x s c bs e suf = do
  ct <- ctorTy γ c s
  unapply γ x s bs (removeAbsRef ct) e suf

consRelCheckAltAsyncL :: UnaryTyping -> CGEnv -> RelEnv -> SpecType -> SpecType -> F.Expr ->
  Var -> Var -> SpecType -> CoreExpr -> Alt CoreBndr -> CG ()
consRelCheckAltAsyncL unary γ ψ t1 t2 p x1 x1' s1 e2 (c, bs1, e1) = do
  (γ', e1') <- consExtAltEnv γ (F.symbol x1') s1 c bs1 e1 relSuffixL
  consRelCheck unary γ' ψ (subVarAndTy x1 x1' e1') e2 t1 t2 p

consRelCheckAltAsyncR :: UnaryTyping -> CGEnv -> RelEnv -> SpecType -> SpecType -> F.Expr ->
  CoreExpr -> Var -> Var -> SpecType -> Alt CoreBndr -> CG ()
consRelCheckAltAsyncR unary γ ψ t1 t2 p e1 x2 x2' s2 (c, bs2, e2) = do
  (γ', e2') <- consExtAltEnv γ (F.symbol x2') s2 c bs2 e2 relSuffixR
  consRelCheck unary γ' ψ e1 (subVarAndTy x2 x2' e2') t1 t2 p

-- consRelCheckAltSync :: CGEnv -> RelEnv -> SpecType -> SpecType -> F.Expr ->
--   F.Symbol -> F.Symbol -> SpecType -> SpecType -> RelAlt -> CG ()
-- consRelCheckAltSync γ ψ t1 t2 p x1 x2 s1 s2 (c, bs1, bs2, e1, e2) = do
--   (γ', e1') <- consExtAltEnv γ x1 s1 c bs1 e1 relSuffixL
--   (γ'', e2') <- consExtAltEnv γ' x2 s2 c bs2 e2 relSuffixR
--   consRelCheck γ'' ψ e1' e2' t1 t2 p

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
-- unapply γ y yt l@(_ : _) (RAllP p ty) e suffix = unapply γ y yt l (forgetRAllP p ty) e suffix 
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

consRelSynth :: UnaryTyping -> CGEnv -> RelEnv -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, [F.Expr])
consRelSynth unary γ ψ (Tick tt e) d =
  {- traceSyn "Left Tick" e d -} consRelSynth unary (γ `setLocation` Sp.Tick tt) ψ e d

consRelSynth unary γ ψ e (Tick tt d) =
  {- traceSyn "Right Tick" e d -} consRelSynth unary (γ `setLocation` Sp.Tick tt) ψ e d

consRelSynth unary γ ψ a1@(App e1 d1) e2 | Type t1 <- GM.unTickExpr d1 =
  traceSyn "App Ty L" a1 e2 $ do
    (ft1', t2, ps) <- consRelSynth unary γ ψ e1 e2
    let (α1, ft1, _) = unRAllT ft1' "consRelSynth App Ty L"
    t1' <- trueTy (typeclass (getConfig γ)) t1
    return (subsTyVarMeet' (ty_var_value α1, t1') ft1, t2, ps)

consRelSynth unary γ ψ e1 a2@(App e2 d2) | Type t2 <- GM.unTickExpr d2 =
  traceSyn "App Ty R" e1 a2 $ do
    (t1, ft2', ps) <- consRelSynth unary γ ψ e1 e2
    let (α2, ft2, _) = unRAllT ft2' "consRelSynth App Ty R"
    t2' <- trueTy (typeclass (getConfig γ)) t2
    return (t1, subsTyVarMeet' (ty_var_value α2, t2') ft2, ps)

consRelSynth unary γ ψ a1@(App e1 d1) a2@(App e2 d2) = traceSyn "App Exp Exp" a1 a2 $ do
  (ft1, ft2, fps) <- consRelSynth unary γ ψ e1 e2
  (t1, t2, ps) <- consRelSynthApp unary γ ψ ft1 ft2 fps d1 d2
  -- qs <- instantiateApp a1 a2 γ ψ
  return (t1, t2, ps)

consRelSynth unary γ ψ e d = traceSyn "Unary" e d $ do
  t <- syn unary γ e >>= refreshTy
  s <- syn unary γ d >>= refreshTy
  let ps = lookupRelSig ψ e d t s
  return (t, s, traceWhenLoud ("consRelSynth Unary synthed preds:" ++ F.showpp ps) ps)
    
lookupRelSig :: RelEnv -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> [F.Expr] 
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

consRelSynthApp :: UnaryTyping -> CGEnv -> RelEnv -> SpecType -> SpecType ->
  [F.Expr] -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, [F.Expr])
consRelSynthApp unary γ ψ ft1 ft2 ps e1 (Tick _ e2) =
  consRelSynthApp unary γ ψ ft1 ft2 ps e1 e2
consRelSynthApp unary γ ψ ft1 ft2 ps (Tick t1 e1) e2 =
  -- TODO: create span
  consRelSynthApp unary (γ `setLocation` Sp.Tick t1) ψ ft1 ft2 ps e1 e2

consRelSynthApp unary γ ψ ft1@(RFun v1 _ s1{- @RFun{} -} t1 r1) ft2@(RFun v2 _ s2{- @RFun{} -} t2 r2) ps@[F.PImp q p] d1@(Var x1) d2@(Var x2)
  = traceSynApp ft1 ft2 ps d1 d2 $ do
    entlFunRefts γ r1 r2 "consRelSynthApp HO"
    let qsubst = F.subst $ F.mkSubst [(v1, F.EVar resL), (v2, F.EVar resR)]
    consRelCheck unary γ ψ d1 d2 s1 s2 (qsubst q)
    let subst = F.subst $ F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
    return (subst t1, subst t2, [(subst . unapplyRelArgs v1 v2) p])
consRelSynthApp unary γ ψ ft1@(RFun v1 _ s1 t1 r1) ft2@(RFun v2 _ s2 t2 r2) ps@[] d1@(Var x1) d2@(Var x2)
  = traceSynApp ft1 ft2 ps d1 d2 $ do
    entlFunRefts γ r1 r2 "consRelSynthApp FO"
    chk unary γ d1 s1
    chk unary γ d2 s2
    (_, _, qs) <- consRelSynth unary γ ψ d1 d2
    let subst =
          F.subst $ F.mkSubst
            [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
    return (subst t1, subst t2, map subst qs)
consRelSynthApp _ _ _ RFun{} RFun{} ps d1@(Var _) d2@(Var _)
  = F.panic $ "consRelSynthApp: multiple rel sigs not supported " ++ F.showpp (ps, d1, d2)
-- do
--     entlFunRefts γ r1 r2 "consRelSynthApp FO"
--     consUnaryCheck γ d1 s1
--     consUnaryCheck γ d2 s2
--     let qsubst = F.subst $ F.mkSubst [(v1, F.EVar resL), (v2, F.EVar resR)]
--     (_, _, qs) <- consRelSynth γ ψ d1 d2
--     let subst =
--           F.subst $ F.mkSubst
--             [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
--     return (subst t1, subst t2, map (subst . unapplyRelArgs v1 v2) (qsubst qs ++ ps))
consRelSynthApp _ _ _ RFun{} RFun{} _ d1 d2 =
  F.panic $ "consRelSynthApp: expected application to variables, got" ++ F.showpp (d1, d2)
consRelSynthApp _ _ _ t1 t2 p d1 d2 =
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
  -- consUnaryCheck γ e t
  return $ removeAbsRef t
consUnarySynth _ e@(Cast _ _) = F.panic $ "consUnarySynth is undefined for Cast " ++ F.showpp e
consUnarySynth _ e@(Type _) = F.panic $ "consUnarySynth is undefined for Type " ++ F.showpp e
consUnarySynth _ e@(Coercion _) = F.panic $ "consUnarySynth is undefined for Coercion " ++ F.showpp e

caseKVKind :: [Alt Var] -> KVKind
caseKVKind [(DataAlt _, _, Var _)] = ProjectE
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
-- selfifyExpr (RAllT α t r) f = (\t -> RAllT α t r) <$> selfifyExpr t f
-- selfifyExpr (RAllT α t r) f = (\t -> RAllT α t r) <$> selfifyExpr t (F.ETApp f (F.FVar 0))
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
consUnarySynthApp γ t@RAllP{} e
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
-- Predicate Well-Formedness ---------------------------------
--------------------------------------------------------------

-- wfTruth :: SpecType -> SpecType -> F.Expr
-- wfTruth (RAllT _ t1 _) t2 = wfTruth t1 t2
-- wfTruth t1 (RAllT _ t2 _) = wfTruth t1 t2
-- wfTruth (RFun _ _ _ t1 _) (RFun _ _ _ t2 _) =
--   F.PImp F.PTrue $ wfTruth t1 t2
-- wfTruth _ _ = F.PTrue

--------------------------------------------------------------
-- Helper Definitions ----------------------------------------
--------------------------------------------------------------

containsVars :: F.Visitable t => [F.Symbol] -> t -> Bool
containsVars vs = getAny . F.fold varVis () (Any False)
 where
  varVis = (F.defaultVisitor :: F.Visitor Any t) { F.accExpr = vars' }
  vars' _ (F.EVar v) = Any $ v `elem` vs
  vars' _ _          = Any False

isFuncPred :: F.Expr -> Bool
isFuncPred (F.PImp _ _) = True
isFuncPred _            = False

partitionArg :: Var -> Var -> SpecType -> SpecType -> F.Expr -> (RelEnv, [F.Expr])
partitionArg x1 x2 s1 s2 q = partitionArgs [x1] [x2] [s1] [s2] [q]

partitionArgs :: [Var] -> [Var] -> [SpecType] -> [SpecType] -> [F.Expr] -> (RelEnv, [F.Expr])
partitionArgs xs1 xs2 ts1 ts2 qs = (map toRel ho, map toUnary fo)
 where
  (ho, fo) = L.partition (isFuncPred . toUnary) (zip5 xs1 xs2 ts1 ts2 qs)
  -- unapp    = L.foldl' (\p (v1, v2) -> unapplyRelArgs v1 v2 p)
  toRel (f1, f2, t1, t2, q) =
    let (vs1, ts1') = vargs t1
    in  let (vs2, ts2') = vargs t2
        in  let bs1 = zip vs1 (fst . vargs <$> ts1')
            in  let bs2 = zip vs2 (fst . vargs <$> ts2')
                -- TODO: add symmetric RelPred
                in  let rp = RelPred f1 f2 bs1 bs2 $ ERBasic q
                    in traceWhenLoud ("partitionArgs toRel: " ++ F.showpp (f1, f2, bs1, bs2, q)) rp
  toUnary (_, _, _, _, q) = q

unRAllT :: SpecType -> String -> (RTVU RTyCon RTyVar, SpecType, RReft)
unRAllT (RAllT α2 ft2 r2) _ = (α2, ft2, r2)
unRAllT t msg = F.panic $ msg ++ ": expected RAllT, got: " ++ F.showpp t

forgetRAllP :: PVU RTyCon RTyVar -> SpecType -> SpecType
forgetRAllP _ t = t

-- isCtor :: Ghc.DataCon -> F.Expr -> F.Expr
-- isCtor d = F.EApp (F.EVar $ makeDataConChecker d)

-- isAltCon :: AltCon -> F.Symbol -> F.Expr
-- isAltCon (DataAlt c) x | c == Ghc.trueDataCon  = F.EVar x
-- isAltCon (DataAlt c) x | c == Ghc.falseDataCon = F.PNot $ F.EVar x
-- isAltCon (DataAlt c) x                         = isCtor c (F.EVar x)
-- isAltCon _           _                         = F.PTrue

-- isBoolDataCon :: DataCon -> Bool
-- isBoolDataCon c = c == Ghc.trueDataCon || c == Ghc.falseDataCon

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

binderToExpr :: CoreBind -> CoreExpr
binderToExpr (NonRec _ e) = e
binderToExpr (Rec ((_, e):_)) = e
binderToExpr _ = F.panic "binderToExpr: no expr in binder"

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

-- conclRel :: RelExpr -> F.Expr
-- conclRel (ERBasic e      ) = e
-- conclRel (ERChecked   _ b) = conclRel b
-- conclRel (ERUnChecked _ b) = conclRel b

concl :: F.Expr -> F.Expr
concl (F.PImp _ p) = concl p
concl p            = p

-- unpackApp :: CoreExpr -> Maybe [Var]
-- unpackApp = fmap reverse . unpack' . GM.unTickExpr
--  where
--   unpack' :: CoreExpr -> Maybe [Var]
--   unpack' (Tick _ e)                      = unpack' e
--   unpack' (Var f   )                      = Just [f]
--   unpack' (App e (Var α)) | Ghc.isTyVar α = unpack' e
--   unpack' (App e (Type _))                = unpack' e
--   unpack' (App e (Var  x))                = (x :) <$> unpack' e
--   unpack' e = traceWhenLoud ("can't unpackApp APP " ++ show e) Nothing

-- instantiateApp :: CoreExpr -> CoreExpr -> CGEnv -> RelEnv -> CG [F.Expr]
-- instantiateApp e1 e2 γ ψ = traceWhenLoud
--   ("instantiateApp " ++ F.showpp e1 ++ " " ++ F.showpp e2 ++ " " ++ (concatMap ((++ "\n"). show) ψ))
--   concatMapM (inst (unpackApp e1) (unpackApp e2)) ψ
--  where
--   inst :: Maybe [Var] -> Maybe [Var] -> RelPred -> CG [F.Expr]
--   inst (Just (f1:xs1)) (Just (f2:xs2)) qpr
--     | fun1 qpr == f1
--     , fun2 qpr == f2
--     , length (args1 qpr) == length xs1
--     , length (args2 qpr) == length xs2
--     = do
--         p <- traceWhenLoud ("instantiateApp qpr pred: " ++ F.showpp (fromRelExpr (prop qpr)))
--               consTotalHOPred xs1 xs2 (args1 qpr) (args2 qpr) (prop qpr) []
--         return $
--           traceWhenLoud ("instantiateApp: " ++ F.showpp p)
--             [p]
--   inst _ _ _ = return []
--   consTotalHOPred :: [Var] -> [Var] -> [(F.Symbol, [F.Symbol])] -> [(F.Symbol, [F.Symbol])] -> RelExpr -> [F.Expr] -> CG F.Expr
--   consTotalHOPred [] [] [] [] rps qs = return $ if null p then F.PTrue else L.foldr1 F.PImp p
--     where
--       ps = fromRelExpr rps
--       p = reverse qs ++ (prems ps ++ [concl ps])
--   consTotalHOPred (x1:xs1) (x2:xs2) ((b1, bs1@(_:_)):vs1) ((b2, bs2@(_:_)):vs2) ps' qs
--     | Just (q, ps) <- traceWhenLoud ("consTotalHOPred ps' (chk) " ++ F.showpp (fromRelExpr ps')) unImp ps' = do
--         (tf1, tf2, _) <- consRelSynth γ ψ (Var x1) (Var x2)
--         case (tf1, tf2) of
--           (RFun x1' _ _ _ _, RFun x2' _ _ _ _) -> do
--             fqs <- instantiateApp (App (Var x1) (Var evar1)) (App (Var x2) (Var evar2)) γ ψ
--             let fqsub = F.mkSubst [(F.symbol evar1, F.EVar x1'), (F.symbol evar2, F.EVar x2')]
--             let bs2args = zip (bs1 ++ bs2) (F.EVar <$> fst (vargs tf1) ++ fst (vargs tf2))
--             let qsub = F.mkSubst (traceWhenLoud ("subst qpr prem " ++ show bs2args) bs2args)
--             let p = F.subst fqsub $ F.PAnd (unapplyRelArgs (F.symbol x1) (F.symbol x2) <$> fqs)
--             let q' = F.subst qsub q
--             consRelSub γ tf1 tf2 (traceWhenLoud ("consTotalHOPred fqs for (" ++ F.showpp evar1 ++ " " ++ F.showpp evar2 ++ "): "
--                                                   ++ F.showpp fqs ++ " consTotalHOPred p: " ++ F.showpp p) p)
--                                  (traceWhenLoud ("consTotalHOPred q: " ++ F.showpp q') q')
--             let bs2fs = F.mkSubst [(b1, F.EVar (F.symbol x1)), (b2, F.EVar (F.symbol x2))]
--             consTotalHOPred xs1 xs2 vs1 vs2
--                   (substR bs2fs $ unapplyRelArgsR (F.symbol x1) (F.symbol x2) ps) qs
--           _ -> F.panic "consTotalHOPred: bs "
--       where
--         (evar1, evar2) = mkRelCopies x1 x2
--         -- f1 = symbolType γ x1 "consTotalHOPred funArg L"
--         -- f2 = symbolType γ x2 "consTotalHOPred funArg R"
--   consTotalHOPred (x1:xs1) (x2:xs2) ((b1, _):vs1) ((b2, _):vs2) (ERChecked q ps) qs
--         = do
--             (tf1, tf2, _) <- consRelSynth γ ψ (Var x1) (Var x2)
--             fqs <- instantiateApp (Var x1) (Var x2) γ ψ
--             let bs2rs = [(b1, F.EVar resL), (b2, F.EVar resR)]
--             let qsub = F.mkSubst bs2rs
--             let p = F.PAnd (unapplyRelArgs (F.symbol x1) (F.symbol x2) <$> fqs)
--             let q' = F.subst qsub q
--             consRelSub γ tf1 tf2 (traceWhenLoud ("consTotalHOPred fqs: " ++ F.showpp fqs ++ " consTotalHOPred p: " ++ F.showpp p) p)
--                                  (traceWhenLoud ("consTotalHOPred q: " ++ F.showpp q') q')
--             let bs2args = F.mkSubst [(b1, F.EVar (F.symbol x1)), (b2, F.EVar (F.symbol x2))]
--             consTotalHOPred xs1 xs2 vs1 vs2
--                   (substR bs2args $ unapplyRelArgsR (F.symbol x1) (F.symbol x2) ps) qs
--   consTotalHOPred (x1:xs1) (x2:xs2) ((v1, _):vs1) ((v2, _):vs2) (ERUnChecked q ps) qs
--       = consTotalHOPred xs1 xs2 vs1 vs2 (substR sb $ unapplyRelArgsR (F.symbol x1) (F.symbol x2) ps) (F.subst sb <$> q : qs)
--     where
--       sb = F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
--   -- TODO: change the parser to prioritise ERUnChecked q ps
--   consTotalHOPred (x1:xs1) (x2:xs2) ((v1, _):vs1) ((v2, _):vs2) (ERBasic (F.PImp q ps)) qs
--     = consTotalHOPred xs1 xs2 vs1 vs2 (substR sb $ unapplyRelArgsR (F.symbol x1) (F.symbol x2) (ERBasic ps)) (F.subst sb <$> q : qs)
--     where
--       sb = F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
--   consTotalHOPred xs1 xs2 vs1 vs2 ps qs = F.panic $ "consTotalHOPred: number of premises should be >= length of arg list" ++
--                                                     F.showpp xs1 ++ " " ++ F.showpp xs2 ++ " " ++ F.showpp vs1 ++ " " ++ F.showpp vs2 ++
--                                                     " " ++ F.showpp (fromRelExpr ps) ++ " " ++ F.showpp qs

-- substR :: F.Subst -> RelExpr -> RelExpr
-- substR sb (ERChecked p rp) = ERChecked (F.subst sb p) (substR sb rp)
-- substR sb (ERUnChecked p rp) = ERUnChecked (F.subst sb p) (substR sb rp)
-- substR sb (ERBasic p) = ERBasic (F.subst sb p)

extendWithTyVar :: CGEnv -> TyVar -> CG CGEnv
extendWithTyVar γ a
  | isValKind (Ghc.tyVarKind a)
  = γ += ("extendWithTyVar", F.symbol a, kindToRType $ Ghc.tyVarKind a)
  | otherwise
  = return γ

-- unifyAlts :: CoreBndr -> CoreBndr -> [Alt CoreBndr] -> [Alt CoreBndr] -> Maybe [RelAlt]
-- unifyAlts x1 x2 alts1 alts2 = mapM subRelCopiesAlts (zip alts1 alts2)
--   where
--     subRelCopiesAlts ((a1, bs1, e1), (a2, bs2, e2))
--       | a1 /= a2  = Nothing
--       | otherwise = let (e1', e2') = L.foldl' sb (subRelCopies e1 x1 e2 x2) (zip bs1 bs2)
--                      in Just (a1, mkLCopies bs1, mkRCopies bs2, e1', e2')
--     sb (e1, e2) (x1', x2') = subRelCopies e1 x1' e2 x2'

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

subVarAndTys :: [(Var, Var)] -> CoreExpr -> CoreExpr
subVarAndTys xs = subTy (M.fromList xsTyVars) . sub (M.fromList xsVars)
  where 
    xsVars   = map (B.second Var) xs
    xsTyVars = map (B.second TyVarTy) xs

mkRelCopies :: Var -> Var -> (Var, Var)
mkRelCopies x1 x2 = (mkCopyWithSuffix relSuffixL x1, mkCopyWithSuffix relSuffixR x2)

-- mkLCopies :: [Var] -> [Var]
-- mkLCopies = (mkCopyWithSuffix relSuffixL <$>)

-- mkRCopies :: [Var] -> [Var]
-- mkRCopies = (mkCopyWithSuffix relSuffixR <$>)

mkCopyWithName :: String -> Var -> Var
mkCopyWithName s v = 
  -- GM.stringVar s (Ghc.exprType (Var v))
  Ghc.setVarName v $ Ghc.mkSystemName (Ghc.getUnique v) (Ghc.mkVarOcc s)

mkCopyWithSuffix :: String -> Var -> Var
mkCopyWithSuffix s v = mkCopyWithName (Ghc.getOccString v ++ s) v

mkLeftCopies :: [(Var, CoreExpr)] -> [(Var, CoreExpr)]
mkLeftCopies = map (B.first (mkCopyWithSuffix relSuffixL))

mkRightCopies :: [(Var, CoreExpr)] -> [(Var, CoreExpr)]
mkRightCopies = map (B.first (mkCopyWithSuffix relSuffixR))

subOneSideCopies :: CoreExpr -> [(Var, CoreExpr)] -> [(Var, CoreExpr)] -> CoreExpr
subOneSideCopies e bs bs' = L.foldl' (\e' ((x, _), (xr, _)) -> subVarAndTy x xr e') e $ zip bs bs'

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
unapplyRelArgsR x1 x2 (ERBasic e     ) = ERBasic (unapplyRelArgs x1 x2 e)
unapplyRelArgsR x1 x2 (ERChecked e re) = 
  ERChecked
    (ERBasic $ unapplyRelArgs x1 x2 (fromRelExpr e))
    (unapplyRelArgsR x1 x2 re)
unapplyRelArgsR x1 x2 (ERUnChecked e re) =
  ERUnChecked (unapplyRelArgs x1 x2 e) (unapplyRelArgsR x1 x2 re)


exprToUReft :: F.Expr -> RReft
exprToUReft e
  = traceWhenLoud ("exprToUReft " ++ F.showpp e ++ " to " ++ F.showpp r) r
    where r = uTop (F.Reft (F.vv_, F.pAnd [e]))

--------------------------------------------------------------
-- RelExpr & F.Expr ------------------------------------------
--------------------------------------------------------------

fromRelExpr :: RelExpr -> F.Expr
fromRelExpr (ERBasic e) = e
fromRelExpr (ERChecked a b) = F.PImp (fromRelExpr a) (fromRelExpr b)
fromRelExpr (ERUnChecked a b) = F.PImp a (fromRelExpr b)

-- toRelExpr :: F.Expr -> RelExpr
-- toRelExpr (F.PImp a b) = ERUnChecked a (toRelExpr b)
-- toRelExpr p = ERBasic p

-- unImp :: RelExpr -> Maybe (F.Expr, RelExpr)
-- unImp (ERBasic (F.PImp a b)) = Just (a, ERBasic b)
-- unImp (ERChecked a b) = Just (a, b)
-- unImp (ERUnChecked a b) = Just (a, b)
-- unImp _ = Nothing

-- toBasic :: RelExpr -> Maybe F.Expr
-- toBasic (ERBasic e) = Just e
-- toBasic (ERChecked _ _) = Nothing
-- toBasic (ERUnChecked a b) = F.PImp a <$> toBasic b

-- toBasicOr :: F.Expr -> RelExpr -> F.Expr
-- toBasicOr t = MB.fromMaybe t . toBasic


--------------------------------------------------------------
-- Pretty Printing Errors ------------------------------------
--------------------------------------------------------------

relWfError :: F.SourcePos -> Ghc.Var -> Ghc.Var -> SpecType -> SpecType -> RelExpr -> String -> Error
relWfError loc e1 e2 t1 t2 p msg
  = ErrRelationalWf 
      (GM.fSrcSpan loc)
      (F.symbol e1)
      (F.symbol e2)
      (text $ F.showpp t1)
      (text $ F.showpp t2)
      (text $ F.showpp p)
      (text msg)

--------------------------------------------------------------
-- Pretty Printing Unary Proofs ------------------------------
--------------------------------------------------------------

relHint :: SpecType -> Ghc.Var -> CoreExpr -> Doc
relHint t v e = text "import GHC.Types"
                $+$ text ""
                $+$ text "{- HLINT ignore \"Use camelCase\" -}"
                $+$ text ("{-@ " ++ F.showpp v
                           ++ " :: "
                           ++ F.showpp t
                           ++ " @-}")
                $+$ text (F.showpp v
                           ++ " :: "
                           ++ removeIdent (toType False t))
                $+$ text (coreToHs t v (fromAnf e))

removeIdent :: Type -> String
removeIdent t = withNoLines noIdent $ F.pprint t

withNoLines :: Style -> Doc -> String
withNoLines style doc = fullRender m l r noSpace "" doc
  where
    m = mode style
    l = lineLength style
    r = ribbonsPerLine style

noSpace :: TextDetails -> String -> String
noSpace (Chr '\n')    s  = ' ':s
noSpace (Chr c)       s  = c:s
noSpace (Str  s1)     s2 = unwords (lines s1) ++ s2
noSpace (PStr s1)     s2 = s1 ++ s2

{- Style for OneLineMode -}
noIdent :: Style
noIdent = Style { mode = OneLineMode
                , lineLength = 0
                , ribbonsPerLine = 0}

--------------------------------------------------------------
-- Debug -----------------------------------------------------
--------------------------------------------------------------

-- showType :: SpecType -> String
-- showType (RAllP _ t  ) = "RAllP " ++ showType t
-- showType (RAllT _ t _) = "RAllT " ++ showType t
-- showType (RImpF _ _ t t' _) =
--   "RImpF(" ++ showType t ++ ", " ++ showType t' ++ ") "
-- showType (RFun _ _ t t' _) = "RFun(" ++ showType t ++ ", " ++ showType t' ++ ") "
-- showType (RAllE _ t t' ) = "RAllE(" ++ showType t ++ ", " ++ showType t' ++ ") "
-- showType (REx   _ t t' ) = "REx(" ++ showType t ++ ", " ++ showType t' ++ ") "
-- showType (RAppTy t t' _) =
--   "RAppTy(" ++ showType t ++ ", " ++ showType t' ++ ") "
-- showType (RApp _ ts _ _) = "RApp" ++ show (showType <$> ts)
-- showType (RRTy xts _ _ t) =
--   "RRTy("
--     ++ show (map (\(_, s) -> showType s) xts)
--     ++ ", "
--     ++ showType t
--     ++ ") "
-- showType v@(RVar _ _  ) = "RVar " ++ F.showpp v
-- showType v@(RExprArg _) = "RExprArg " ++ F.showpp v
-- showType v@(RHole    _) = "RHole" ++ F.showpp v

-- traceUnapply :: (PPrint x1, PPrint x2, PPrint e1, PPrint e2) => x1 -> x2 -> e1 -> e2 -> e2
-- traceUnapply x1 x2 e1 e2 = traceWhenLoud ("Unapply\n"
--                       ++ "x1: " ++ F.showpp x1 ++ "\n\n"
--                       ++ "x2: " ++ F.showpp x2 ++ "\n\n"
--                       ++ "e1: " ++ F.showpp e1 ++ "\n\n"
--                       ++ "e2: " ++ F.showpp e2) e2


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
