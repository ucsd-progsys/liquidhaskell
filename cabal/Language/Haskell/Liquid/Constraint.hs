{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}

{- Representation of Sub and WF Constraints, 
 - and code for syntax-directed constraint generation. -}

module Language.Haskell.Liquid.Constraint (
    generateConstraints
  , CGInfo (..)
  , kvars, kvars' -- symbols  -- debugging purposes
  ) where

import Id               (isDataConId_maybe)
import SrcLoc           
import CoreSyn
import Type             -- (coreEqType)
import PrelNames
import TysPrim
import TysWiredIn
import qualified TyCon as TC

import Type             (mkTyConTy)
import TypeRep 
import Unique       -- (getUnique, getKey)
import Class            (Class, className)
import PrelNames        (eqClassName, ordClassName)
import PrelInfo         (isNumericClass)
import Var
import Name             (getSrcSpan)
import VarEnv
import Outputable   hiding (empty)
import TysWiredIn   
import DataCon 
import Control.Monad.State
import Control.Monad.Reader

import Control.Exception.Base
import Control.Applicative      ((<$>))
import Data.Maybe (isJust, maybeToList, fromJust, fromMaybe)
import qualified Data.Map as M
import Data.List (inits, find, foldl')
import qualified Data.Set as S
import Text.Printf

import qualified Language.Haskell.Liquid.Fixpoint as F
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Haskell.Liquid.GhcInterface 
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType hiding (splitArgsRes)
import Language.Haskell.Liquid.Predicates
import Language.Haskell.Liquid.GhcMisc2 (tickSrcSpan)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.MiscExpr (exprType)
import Language.Haskell.Liquid.Bare (isDummyBind)

import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq

-----------------------------------------------------------------------
------------------------ Generation: Toplevel -------------------------
-----------------------------------------------------------------------

consGrty γ (x, t) 
  = addC (SubC γ (γ ?= (mkSymbol x)) t) ""

consAct info penv
  = do γ <- initEnv info penv
       γ1  <- foldM consCB γ $ cbs info
       forM_ (grty info) (consGrty γ1)

generateConstraints :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} st { fixCs = fcs} { fixWfs = fws } { globals = gs }
  where st  = execState act (initCGI info)
        act = consAct (info{cbs = fst pds}) (snd pds)
        fcs = concatMap splitC $ hsCs  st 
        fws = concatMap splitW $ hsWfs st
        gs  = F.fromListFEnv . map (mapSnd refTypeSortedReft) $ meas info
        pds = generatePredicates info
        cns = M.fromList (tconsP info)

kvars :: (Data a) => a -> S.Set F.Symbol
kvars = everything S.union (S.empty `mkQ` grabKvar)
  where grabKvar (F.RKvar k _) = S.singleton k
        grabKvar _             = S.empty


kvars' :: (Data a) => a -> Int
kvars' = everything (plus') (0 `mkQ` grabKvar)
  where grabKvar (F.RKvar k _) = 1 
        grabKvar _             = 0
        plus' !x !y            = x + y 

--symbols :: (Data a) => a -> S.Set F.Symbol
--symbols = everything S.union (S.empty `mkQ` grab)
--  where grab x@(F.S _) = S.singleton x 


initEnv :: GhcInfo -> PEnv -> CG CGEnv  
initEnv info penv
  = do defaults <- forM freeVars $ \x -> liftM (x,) (trueTy $ varType x)
       tyi      <- liftM tyConInfo get 
       let f0  = defaults     -- default TOP reftype      (for all vars) 
       let f1  = wiredIn info -- builtins                 (for prims like I#)
       let f2  = assm info    -- assumed refinements      (for import ANNs)
       let f3  = ctor info    -- constructor refinements  (for measures) 
       let bs  = ((mapSnd (addTyConInfo tyi)) . unifyts penv 
                      <$> concat [f0, f1, f2, f3])
       return  $ foldl' (++=) (measEnv info penv) bs 
    where freeVars = importVars $ cbs info

unifyts penv (x, t) = (x', unify pt t)
 where pt = lookupPEnv x' penv
       x' = mkSymbol x
   
measEnv info penv = CGE noSrcSpan re0 penv fe0 S.empty
  where bs   = meas info 
        re0  = fromListREnv bs 
        fe0  = F.fromListFEnv $ mapSnd refTypeSortedReft <$> bs 


-------------------------------------------------------------------
-------- Helpers: Reading/Extending Environment Bindings ----------
-------------------------------------------------------------------

data CGEnv = CGE { loc  :: !SrcSpan      -- where in orig src
                 , renv :: !REnv         -- bindings in scope
                 , penv :: !PEnv         -- bindings in scope
                 , fenv :: !F.Envt       -- the fixpoint environment 
                 , recs :: !(S.Set Var)  -- recursive defs being processed (for annotations)
                 } deriving (Data, Typeable)

instance Outputable CGEnv where
  ppr = ppr . renv

instance Show CGEnv where
  show = showPpr

{- see tests/pos/polyfun for why you need everything in fixenv -} 
γ ++= (x, r') 
  | isBase r 
  = γ' { fenv = F.insertFEnv x (refTypeSortedReft r) (fenv γ) }
  | otherwise
  = γ' { fenv = insertFEnvClass r (fenv γ) }
  where γ' = γ { renv = insertREnv x r (renv γ) }  
        r  = normalizePds r'  -- move pred abs in start of the type

(γ, msg) += (x, r) 
  | x `memberREnv` (renv γ)
  = errorstar $ "ERROR: " ++ msg ++ " Duplicate Binding for " ++ show x ++ " in REnv!\n\n" ++ show γ
  | otherwise
  = γ ++= (x, r) 

γ -= x 
  =  γ { renv = deleteREnv x (renv γ) } { fenv = F.deleteFEnv x (fenv γ) }

(?=) ::  CGEnv -> F.Symbol -> RefType 
γ ?= x
  = case lookupREnv x (renv γ) of
      Just t  -> t
      Nothing -> errorstar $ "EnvLookup: unknown = " ++ showPpr x

getPrType :: CGEnv -> F.Symbol -> Maybe PrType
getPrType γ x = lookupPEnv x (penv γ)

atLoc :: CGEnv -> SrcSpan -> CGEnv
γ `atLoc` src 
  | isGoodSrcSpan src = γ { loc = src } 
  | otherwise         = γ

withRecs :: CGEnv -> [Var] -> CGEnv 
withRecs γ xs = γ { recs = foldl' (flip S.insert) (recs γ) xs }

isGeneric :: RTyVar -> RefType -> Bool
isGeneric α t =  all (\(c, α') -> (α'/=α) || isOrd c || isEq c ) (classConstrs t)
  where classConstrs t = [(c, α') | (c, ts) <- getTyClasses t
		                                , t'      <- ts
																													     , α'      <- getTyVars t']
        isOrd          = (ordClassName ==) . className
        isEq           = (eqClassName ==) . className

getTyClasses = everything (++) ([] `mkQ` f)
  where f ((RClass c ts) :: RefType) = [(c, ts)]
        f _                          = []

getTyVars = everything (++) ([] `mkQ` f)
  where f ((RVar α' _) :: RefType)   = [α'] 
        f _                          = []
 
isBase :: RType a -> Bool
isBase (RVar _ _)        = True
isBase (RConApp _ _ _ _) = True
isBase _                 = False

insertFEnvClass :: RefType -> F.Envt -> F.Envt
insertFEnvClass (RClass c ts) fenv
  | isNumericClass c
  = foldl' (\env x -> F.insertFEnv x numReft env) fenv numVars
  where numReft = F.trueSortedReft F.FNum
        numVars = [rTyVarSymbol a | (RVar a _) <- ts]
insertFEnvClass _ fenv 
  = fenv

-----------------------------------------------------------------
------------------- Constraints: Types --------------------------
-----------------------------------------------------------------

newtype Cinfo = Ci SrcSpan deriving (Data, Typeable)

data SubC     = SubC { senv  :: !CGEnv
                     , lhs   :: !RefType
                     , rhs   :: !RefType 
                     } deriving (Data, Typeable)

data WfC      = WfC  { wenv  :: !CGEnv
                     , r     :: !RefType 
                     } 
              | WfCS { wenv  :: !CGEnv
																					, ty    :: !Type
																					, s     :: !F.Refa
																					}
              deriving (Data, Typeable)

type FixSubC  = F.SubC Cinfo
type FixWfC   = F.WfC Cinfo

instance Outputable SubC where
  ppr c = ppr (senv c) <> text "\n" <> text " |- " <> 
          ppr (lhs c) <> text " <: " <> ppr (rhs c) <> 
          text "\n\n"

instance Outputable WfC where
  ppr w = ppr (wenv w) <> text "\n" <> text " |- " <> ppr (r w) <> 
          text "\n\n" 

instance Outputable Cinfo where
  ppr (Ci src) = ppr src


--instance Outputable a => Outputable (F.SubC a) where
--  -- ppr (F.SubC {F.sinfo = s}) = text "Liquid Type Error: " <> ppr s
--  ppr
--
--
--instance Outputable a => Outputable (F.WfC a) where
--  ppr (F.SubC {F.sinfo = s}) = text "Liquid Type Error: " <> ppr s

------------------------------------------------------------
------------------- Constraint Splitting -------------------
------------------------------------------------------------

splitW ::  WfC -> [FixWfC]

splitW (WfCS γ τ s) 
  = [F.WfC env' r' Nothing ci] 
  where env' = fenv γ
        r'   = typeSortedReft τ s
        ci   = Ci (loc γ)


splitW (WfC γ (RFun (RB x) r1 r2)) 
  =  splitW (WfC γ r1) 
  ++ splitW (WfC ((γ, "splitW") += (x, r1)) r2)

splitW (WfC γ (RAll a r)) 
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ r))
  =  bsplitW γ t 

splitW (WfC γ (RClass _ _))
  = []

splitW (WfC γ t@(RConApp c ts rs _))
  = {-trace ("SplitWf :" ++ show t) $-} bsplitW γ t
		++ concatMap (splitW . WfC γ) ts
		++ concatMap (rsplitW γ) (zip rs ps)
				where ps =  rTyConPs c --[] -- p for r to find its type

splitW (WfC _ t) 
  = [] -- errorstar $ "splitW cannot handle: " ++ showPpr t

{-
splitWRefTyCon γ (RAlgTyCon _ z) 
  = splitWRefAlgRhs cons γ z 
splitWRefTyCon _   _               
  = []

splitWRefAlgRhs γ (RDataTyCon _ dcs) 
  = concatMap (splitWRefDataCon γ) dcs

splitWRefDataCon γ (MkRData _ fts) 
 = concatMapi splitW $ zipWith WfC γs ts
   where ts  = snd <$> fts
         γs  = scanl (\γ z -> (γ, "splitWRefDC") += z) γ (fieldBinds fts)
-}

bsplitW :: CGEnv -> RefType -> [FixWfC]
bsplitW γ t 
  | F.isNonTrivialSortedReft r'
  = [F.WfC env' r' Nothing ci] 
  | otherwise
  = []
  where env' = fenv γ
        r'   = refTypeSortedReft t
        ci   = Ci (loc γ)

rsplitW :: CGEnv -> (F.Reft, Predicate) -> [FixWfC]
rsplitW γ (r, (PdVar _ t as))
  = [F.WfC env' r' Nothing ci]
  where env' = fenv γ'
        ci   = Ci (loc γ)
        r'   = refTypePredSortedReft_ (r, t)
        γ'   = foldl' (++=) γ (map (\(τ, x, _) -> (x, ofType τ)) as) 

------------------------------------------------------------
splitC :: SubC -> [FixSubC]
------------------------------------------------------------
splitC (SubC γ t1@(RFun (RB x1) r1 r1') t2@(RFun (RB x2) r2 r2')) 
  = splitC (SubC γ r2 r1) ++ splitC (SubC γ' r1x2' r2') 
    where r1x2' = r1' `F.subst1` (x1, F.EVar x2) 
          γ'    = (γ, "splitC") += (x2, r2) 

splitC (SubC γ (RAll _ r1) (RAll _ r2)) 
  = splitC (SubC γ r1 r2) 

splitC (SubC γ t1@(RConApp c t1s r1s _) t2@(RConApp c' t2s r2s _))
	= -- traceShow ("Split " ++ show ps ++ "\n" ++ show t1 ++ "\n < \n" ++ show t2 ) $   
 bsplitC γ t1 t2
	++ concatMap splitC (zipWith (SubC γ) t1s t2s)
 ++ concatMap (rsplitC γ) (zip (zip r1s r2s) ps)
--	++ concatMap (rsplitC γ) (zip r1s r2s)
				where ps = rTyConPs c'

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _)) 
  | a1 == a2
  = bsplitC γ t1 t2

splitC (SubC _ (RClass c1 _) (RClass c2 _)) -- | c1 == c2
  = []

splitC (SubC _ t1 t2) 
  = -- traceShow ("\nWARNING: splitC mismatch:\n" 
				--														++ showPpr t1 ++ "\n<\n" ++ showPpr t2 ++ "\n") $
     []

{-
splitCRefTyCon cons γ (RAlgTyCon _ z1) (RAlgTyCon _ z2) 
  = splitCRefAlgRhs cons γ z1 z2 
splitCRefTyCon _ _ _ _               
  = []

splitCRefAlgRhs cons γ (RDataTyCon _ dcs1) (RDataTyCon _ dcs2) 
  = concat $ zipWith (splitCRefDataCon cons γ) dcs1 dcs2

splitCRefDataCon cons γ (MkRData _ fts1) (MkRData _ fts2) 
  = {-traceShow ("\nTrue split :" ++ showPpr t1s ++ "\n" ++ showPpr t2s') $-} concatMap (splitC cons) $!! zipWith3 SubC γs t1s t2s'
    where γs         = scanl (\γ z -> (γ, "splitCRefDC") += z) γ (fieldBinds fts1) 
          t2s'       = zipWith F.subst subs t2s 
          (x1s, t1s) = unzip (fieldBinds fts1)
          (x2s, t2s) = unzip (fieldBinds fts2) 
          x2x1s      = zip x2s $ F.EVar <$> x1s
          subs       = F.mkSubst <$> inits x2x1s
-}

fieldBinds fts = [(x,t) | (RB x, t) <- fts]

bsplitC γ t1 t2 
  | F.isNonTrivialSortedReft r2'
  = [F.SubC γ' F.PTrue r1' r2' Nothing [] ci]
  | otherwise
  = []
  where γ'      = fenv γ
        r1'     = refTypeSortedReft t1
        r2'     = refTypeSortedReft t2
        ci      = Ci (loc γ)

rsplitC γ ((r1, r2), PdVar _ t as)
  = [F.SubC env' F.PTrue r1' r2' Nothing [] ci]
  where env' = fenv γ'
        ci   = Ci (loc γ)
        r1'  = refTypePredSortedReft_ (r1, t)
        r2'  = refTypePredSortedReft_ (r2, t)
        γ'   = foldl' (++=) γ (map (\(τ, x, _) -> (x, ofType τ)) as) 

-----------------------------------------------------------
-------------------- Generation: Types --------------------
-----------------------------------------------------------

newtype CGSpec = CGSpec (Ms.Spec F.Sort DataCon)

data CGInfo = CGInfo { hsCs       :: ![SubC]
                     , hsWfs      :: ![WfC]
                     , fixCs      :: ![FixSubC]
                     , fixWfs     :: ![FixWfC] 
                     , globals    :: !F.Envt -- [(F.Symbol, F.SortedReft)] 
                     , freshIndex :: !Integer 
                     , annotMap   :: !(AnnInfo Annot) 
                     , tyConInfo  :: !(M.Map TC.TyCon RTyCon) 
                     } deriving (Data, Typeable)

instance Outputable CGInfo where 
  ppr cgi =  {-# SCC "ppr_CGI" #-} ppr_CGInfo cgi

ppr_CGInfo cgi 
  =  (text "*********** Haskell-SubConstraints ***********")
  $$ (ppr $ hsCs  cgi)
  $$ (text "*********** Haskell-WFConstraints ************")
  $$ (ppr $ hsWfs cgi)
  $$ (text "*********** Fixpoint-SubConstraints **********")
  $$ (ppr $ fixCs cgi)
  $$ (text "*********** Fixpoint-WFConstraints ************")
  $$ (ppr $ fixWfs cgi)




type CG = State CGInfo

initCGI info = CGInfo [] [] [] [] F.emptyFEnv 0 (AI M.empty) tyi
		where tyi  = M.fromList $ mkTyCon_ {-(\(ty, TyConP _ ps) -> (ty, RTyCon ty ps []))-}  <$> (tconsP info)

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "

mkTyCon_ (tc, (TyConP τs' ps)) = (tc, RTyCon tc ps' [])
  where τs = TyVarTy <$> TC.tyConTyVars tc
        ps' = (subsTyVarsP (zip τs' τs)) <$> ps

addC   :: SubC -> String -> CG ()  
addC !c@(SubC _ t1 t2) s 
  = -- trace ("addC " ++ show t1 ++ "\n < \n" ++ show t2 ++ s) $  
    modify $ \s -> s { hsCs  = c : (hsCs s) }

addW   :: WfC -> CG ()  
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

addIdA :: Var -> Annot -> CG ()
addIdA !x !t = modify $ \s -> s { annotMap = addA l v t $ annotMap s } 
  where l  = getSrcSpan x
        v  = Just x

addLocA :: SrcSpan -> Annot -> CG ()
addLocA !l !t 
  = modify $ \s -> s { annotMap = addA l Nothing t $ annotMap s }

--withSrc :: SrcSpan -> CG a -> CG a
--withSrc loc act 
--  = (modify $ \s -> s {src = loc}) >> act

addA !l !xo !t !a@(AI m) 
  | isGoodSrcSpan l && not (l `M.member` m)
  = AI $ M.insert l (xo, t) m
  | otherwise
  = a
  -- errorstar $ "Duplicate annot " ++ showPpr xo ++ " at " ++ showPpr l

-------------------------------------------------------------------
------------------------ Generation: Freshness --------------------
-------------------------------------------------------------------

-- To revert to the old setup, just do
-- freshTy_pretty = freshTy
freshTy_pretty e τ = refresh $ {-traceShow ("exprRefType: " ++ showPpr e) $-} exprRefType e

-- freshTy_pretty e τ = refresh $ traceShow ("exprRefType: " ++ showPpr e) $ exprRefType e
-- freshTy_pretty e τ = errorstar "GO TO HELL"

-- freshTy :: a -> Type -> CG RefType
freshTy' _ = refresh . ofType 

freshTy :: CoreExpr -> Type -> CG RefType
freshTy e τ = freshTy' e τ 

trueTy  :: Type -> CG RefType
trueTy t 
 = do t <- true $ ofType t
      tyi <- liftM tyConInfo get
      return $ addTyConInfo tyi t

class Freshable a where
  fresh   :: CG a
  true    :: a -> CG a
  true    = return . id
  refresh :: a -> CG a
  refresh = return . id

instance Freshable Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

instance Freshable F.Symbol where
  fresh = liftM (F.tempSymbol "x") fresh

instance Freshable RBind where
  fresh = liftM RB fresh 

instance Freshable F.Refa where
  fresh = liftM (`F.RKvar` F.emptySubst) freshK
    where freshK = liftM F.intKvar fresh

instance Freshable [F.Refa] where
  fresh = liftM single fresh

instance Freshable F.Reft where
  fresh = errorstar "fresh Reft"
  true    (F.Reft (v, _)) = return $ F.Reft (v, []) 
  refresh (F.Reft (v, _)) = liftM (F.Reft . (v, )) fresh

instance Freshable RefType where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

{-
instance Freshable RefTyCon where
  fresh   = errorstar "fresh RefTyCon"
  refresh = refreshRefTyCon
  true    = trueRefTyCon
 
instance Freshable RefAlgRhs where
  fresh   = errorstar "fresh RefTyCon"
  refresh = refreshRefAlgRhs 
  true    = trueRefAlgRhs

instance Freshable RefDataCon where
  fresh   = errorstar "fresh RefTyCon"
  refresh = refreshRefDataCon
  true    = trueRefDataCon
-}

trueRefType (RAll α t)       
  = liftM (RAll α) (true t)
trueRefType (RFun _ t t')    
  = liftM3 RFun fresh (true t) (true t')
trueRefType (RConApp c ts refs _)  
  = liftM (\ts -> RConApp c ts truerefs (F.trueReft)) (mapM true ts)
		where truerefs = (\_ -> F.trueReft)<$> (rTyConPs c)
trueRefType t                
  = return t

{-		
trueRefTyCon (RAlgTyCon p r)  
  = liftM (RAlgTyCon p) (true r)
trueRefTyCon x@(RPrimTyCon _) 
  = return x
trueRefAlgRhs (RDataTyCon p dcs) 
  = liftM (RDataTyCon p) (mapM true dcs)
trueRefDataCon (MkRData p fts) 
  = liftM (MkRData p) $ liftM2 zip (mapM (\_ -> fresh) fs) (mapM true ts)
    where (fs, ts) = unzip fts
-}

refreshRefType (RAll α t)       
  = liftM (RAll α) (refresh t)
refreshRefType (RFun b t t')
  | isDummyBind b
  = liftM3 RFun fresh (refresh t) (refresh t')
  | otherwise
  = liftM2 (RFun b) (refresh t) (refresh t')
refreshRefType (RConApp (rc@RTyCon {rTyCon = c}) ts rs r)  
  = do s <- get 
       let RTyCon c0 ps ids = M.findWithDefault rc c $ tyConInfo s
       let c' = RTyCon c0 (map (subsTyVarsP (zip (TC.tyConTyVars c0) (toType <$> ts))) ps) ids
       liftM3 (RConApp c') (mapM refresh ts) (mapM freshReftP (rTyConPs c')) (refresh r)
refreshRefType (RVar a r)  
  = liftM (RVar a) (refresh r)
refreshRefType t                
  = return t

{-
refreshRefTyCon x@(RAlgTyCon p r)  
  | isBaseTyCon p
  = return x
  | otherwise
  = liftM (RAlgTyCon p) (refresh r)
refreshRefTyCon x@(RPrimTyCon _) 
  = return x

refreshRefAlgRhs (RDataTyCon p dcs) 
  = liftM (RDataTyCon p) (mapM refresh dcs)

refreshRefDataCon (MkRData p fts) 
  = liftM (MkRData p) $ liftM2 zip (mapM (\_ -> fresh) fs) (mapM refresh ts)
    where (fs, ts) = unzip fts
-}

isBaseTyCon c
  | c == intTyCon 
  = True
  | c == boolTyCon
  = True
  | otherwise
  = False

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------

consCB :: CGEnv -> CoreBind -> CG CGEnv 

consCB γ (Rec xes) 
  = do rts <- mapM (\e -> freshTy_pretty e $ exprType e) es
--       let ts = rts
       let ts = (\(pt, rt) -> unify pt rt) <$> (zip pts rts)
       let γ' = foldl' (\γ z -> (γ, "consCB") += z) (γ `withRecs` xs) (zip vs ts)
       zipWithM_ (cconsE γ') es  ts
       zipWithM_ addIdA xs (Left <$> ts)
       mapM_     addW (WfC γ <$> rts)
       return γ'
    where (xs, es) = unzip xes
          vs       = mkSymbol      <$> xs
          pts      = (getPrType γ) <$> vs

consCB γ b@(NonRec x e)
  = do rt <- consE γ e
--       let t = {-traceShow ("Unify for "  ++ show x' ++ "\n\n"++ show e ++ "\n\n" ++ show rt ++ "\n" ++ show pt ++ "\n")$-} rt
       let t = {-traceShow ("Unify for "  ++ show x' ++ "\n\n"++ show e ++ "\n\n" ++ show rt ++ "\n" ++ show pt ++ "\n")$-} unify pt rt
       addIdA x (Left t)
       return $ γ ++= (x', t)
    where x' = mkSymbol x
          pt = getPrType γ x'

-------------------------------------------------------------------
------------------ Unify PrType with RefType ----------------------
-------------------------------------------------------------------

-------------------------------------------------------------------
unify :: Maybe PrType -> RefType -> RefType 
-------------------------------------------------------------------

unify (Just pt) rt  = evalState (unifyS rt pt) S.empty
unify _         t   = t

unifyS :: RefType -> PrType -> State (S.Set Predicate) RefType

-- unifyS t@(RPred _ _) _ 
--   = return t

unifyS (RPred p t) pt
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) 
        then return $ RPred p t'
								else return t'

unifyS t (PrAllPr p pt)
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) 
        then return $ RPred p t'
								else return t'

unifyS (RAll v t) (PrAll v' pt) 
  = do t' <-  unifyS t $ subsTyVars (v', PrVar (toTyVar v) PdTrue) pt 
       return $ RAll v t'

unifyS (RFun (RB x) rt1 rt2) (PrFun x' pt1 pt2)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 (substSym (x', x) pt2)
       return $ RFun (RB x) t1' t2' 

unifyS t@(RClass c _) (PrClass _ _)
  = return t

--unifyS (RVar v a) (PrVar v' PdTrue)
--  = return $ RVar v a 

unifyS (RVar v a) (PrVar v' p)
  = do modify $ \s -> s `S.union` (S.fromList (filter (/= PdTrue) [p]))
       return $ RVar v $ bUnify a p

unifyS rt@(RConApp c ts rs r) pt@(PrTyCon _ pts ps p)
  = do modify $ \s -> s `S.union` (S.fromList (filter (/= PdTrue) (p:ps)))
       ts' <- zipWithM unifyS ts pts
       return $ {-traceShow ("unifyS \n" ++ show rt ++ "\nwith \n" ++ show pt) $-}  RConApp c ts' (mapbUnify rs ps) (bUnify r p)

unifyS t1 t2 = error ("unifyS" ++ show t1 ++ " with " ++ show t2)


bUnify a PdTrue  = a
bUnify a p       = a `F.meet` (pToReft p)

--mapbUnify [] ps = zipWith bUnify (cycle [F.trueReft]) ps
mapbUnify rs ps = zipWith bUnify (rs ++ cycle [F.trueReft]) ps

--pToRefa (PdVar n t a)= F.strToRefa n 
pToRefa (PdVar n t a)= F.strToRefa n ((\(_, x, y) -> (x, F.EVar y)) <$> a)
pToReft (PdVar n t a)= F.strToReft n ((\(_, x, y) -> (x, F.EVar y)) <$> a)
--pToReft (PdVar n t a)= F.strToReft n  
-------------------------------------------------------------------
-------------------- Generation: Expression -----------------------
-------------------------------------------------------------------

-------------------------------------------------------------------
cconsE :: CGEnv -> Expr Var -> RefType -> CG () 
-------------------------------------------------------------------

cconsE γ (Let b e) t    
  = do γ'  <- consCB γ b
       cconsE γ' e t 

cconsE γ ex@(Case e x τ cases) t 
  = do γ'  <- consCB γ $ NonRec x e
       forM_ cases $ cconsCase γ' x t

cconsE γ (Lam α e) (RAll _ t) | isTyVar α
  = cconsE γ e t

cconsE γ (Lam x e) (RFun (RB y) ty t) 
  | not (isTyVar x) 
  = do cconsE ((γ, "cconsE") += (mkSymbol x, ty)) e te 
       addIdA x (Left ty) 
    where te = t `F.subst1` (y, F.EVar $ mkSymbol x)

cconsE γ (Tick tt e) t   
  = cconsE (γ `atLoc` tickSrcSpan tt) e t

cconsE γ (Cast e _) t     
  = cconsE γ e t 
{-
cconsE γ e (RPred p t)
  = do s <- freshSort γ p
       let t' =  replaceSort (pToRefa p, s) t 
--       addC (SubC γ te t) ("consEPRed" ++ showPpr e)
       cconsE γ e t'
-}
cconsE γ e t
  = do te <- consE γ e
       addC (SubC γ te t) ("consE" ++ showPpr e)


-------------------------------------------------------------------
consE :: CGEnv -> Expr Var -> CG RefType 
-------------------------------------------------------------------

--subsTyVarHelper x y = x `subsTyVar` y 
-- {- trace ("PLUGGING" ++ (show x) ++ " into " ++ (show y) ++ " yields " ++ (show res)) $ -} 

foo γ (Var x) = "varTy\n" ++ show   ( γ ?= (mkSymbol x))
foo γ _ = ""


consE γ (Var x)   
  = do addLocA (loc γ) (varAnn γ x t)
       return t
    where t = varRefType γ x

consE _ (Lit c) 
  = return $ literalRefType c

consE γ (App e (Type τ)) 
  = do RAll α te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       t         <- if isGeneric α te then freshTy e τ else  trueTy τ
       addW       $ WfC γ t
       return     $ 
--         traceShow ("type app: for " ++ showPpr e ++ showPpr (α, t) ++ (foo γ e) ++ "/n") $ 
								(α, t) `subsTyVar_meet` te

consE γ e'@(App e a) | eqType (exprType a) predType 
  = do t0 <- consE γ e
       case t0 of
         RPred p@(PdVar pn τ pa) t -> do s <- freshSort γ p
                                         return $ replaceSort (pToRefa p, s) t 
         t                         -> return t
consE γ e'@(App e a)               
  = do RFun (RB x) tx t <- liftM (checkFun ("Non-fun App with caller", e)) $ consE γ e 
       cconsE γ a tx 
       case argExpr a of 
         Just e  -> return 
--                      $ traceShow ("App" ++ showPpr e' ++ show (t, tx)) 
                      $ t `F.subst1` (x, e)
         Nothing -> errorstar $ "consE: App crashes on" ++ showPpr a 

consE γ (Lam α e) | isTyVar α 
  = liftM (RAll (rTyVar α)) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy (Var x) τx 
       t1     <- consE ((γ, "consE") += (mkSymbol x, tx)) e1
       addIdA x (Left tx) 
       addW   $ WfC γ tx 
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

consE env e	    
  = errorstar $ "consE cannot handle " ++ showPpr e

cconsFreshE γ e
  = do t   <- freshTy e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

cconsCase :: CGEnv -> Var -> RefType -> (AltCon, [Var], CoreExpr) -> CG ()

cconsCase γ _ t (DEFAULT, _, ce) 
  = cconsE γ ce t

cconsCase γ x t (DataAlt c, ys, ce) 
  = cconsE cγ ce t
  where cγ            = addBinders γ x' (zip (x':ys') (xt:yts))
        xt0           = checkTyCon x $ γ ?= x'
        td            = γ ?= (dataConSymbol c)
        (rtd, yts, _) = unfoldR td xt0 ys'
        (x':ys')      = mkSymbol <$> (x:ys)
        r1            = dataConReft c $ varType x
        r2            = dataConMsReft rtd ys'
        xt            = xt0 `strengthen` (r1 `F.meet` r2)

unfoldR td t0@(RConApp tc ts rs _) ys = (rtd, yts, xt')
  where (vs, ps, td_')  = rsplitVsPs td
        td''            = foldl' (flip subsTyVar_meet) td' (zip vs ts)
        rtd             = foldl' (flip replaceSort) td'' (zip ps' rs')
        ps'             = reverse $ pToRefa <$> ps
        rs'             = map  (\(F.Reft(_, [r])) -> F.subst su r) (rs) ++ cycle [F.trueRefa]
        (ys', yts, xt') = rsplitArgsRes rtd
        su              = F.mkSubst [(x, F.EVar y) | (x, y)<- zip ys' ys]
        td'             = td_' 
{-
cconsCase γ x t (DataAlt c, ys, ce) 
  = do let (x':ys')      = mkSymbol <$> (x:ys)
       let xt0           = checkTyCon x $ γ ?= x'
       let td            = γ ?= (dataConSymbol c)
       (rtd, yts, _)     <- unfoldR γ td xt0 
       let r1            = dataConReft c $ varType x
       let r2            = dataConMsReft rtd ys'
       let xt            = xt0 `strengthen` (r1 `F.meet` r2)
       let cγ            = addBinders γ x' (zip (x':ys') (xt:yts))
       cconsE cγ ce t

--unfoldR :: RType F.Reft-> RType F.Reft -> (RType F.Reft, [RType F.Reft], RType F.Reft)
unfoldR γ td t0@(RConApp tc ts rs _) 
 = do let (vs, ps, td') = rsplitVsPs td
      let td''          = foldl' (flip subsTyVar_meet) td' (zip vs ts)
      let ps'           = pToRefa <$> ps
      rs''               <- mapM (freshSort γ) ps
      let rs' = case rs of {[] -> map (\r -> F.Reft(F.vv, [r])) rs''; _ -> rs}
      let rtd           = foldl' (flip replaceSorts) td'' (zip ps' rs')
      let (_, yts, xt')    = rsplitArgsRes rtd
      return {-$ traceShow ("unfold " ++ show (td, t0))-} (rtd, yts, xt')
-} 

takeReft c (RConApp _ _ _ a) 
  | c == nilDataCon || c == consDataCon
  = a
  | otherwise
		= F.trueReft
takeReft _ _                
  = F.trueReft

instance Show CoreExpr where
  show = showSDoc . ppr

addBinders γ0 x' cbs 
  = foldl' wr γ2 cbs
    where γ1     = {- traceShow ("addBinders γ0 = " ++ (show $ domREnv $ renv γ0))    $ -} (γ0 -= x')
          wr γ z = {- traceShow ("\nWrapper: keys γ = " ++ (show $ domREnv $ renv γ)) $ -} γ ++= z
          γ2     = if x' `memberREnv` (renv γ1) then error "DIE DIE DIE" else γ1

checkTyCon _ t@(RConApp _ _ _ _) = t
checkTyCon x t                   = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkRPred _ t@(RPred _ _)       = t
checkRPred x t                   = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkFun _ t@(RFun _ _ _)        = t
checkFun x t                     = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkAll _ t@(RAll _ _)          = t
checkAll x t                     = errorstar $ showPpr x ++ "type: " ++ showPpr t


varAnn γ x t 
  | x `S.member` recs γ
  = Right (getSrcSpan' x) 
  | otherwise 
  = Left t

getSrcSpan' x 
  | loc == noSrcSpan
  = trace ("myGetSrcSpan: No Location for: " ++ showPpr x) $ loc
  | otherwise
  = loc
  where loc = getSrcSpan x
   

--instance Outputable Note where
--  ppr (CoreNote s) = text s
--  ppr (SCC c)      = ppr c

-----------------------------------------------------------------------
---------- Helpers: Creating Fresh Refinement ------------------ ------
-----------------------------------------------------------------------
freshReftP (PdVar n τ as)
 = do n <- liftM F.intKvar fresh
      return $ F.Reft(F.vv,[(`F.RKvar` F.emptySubst) n])

freshSort γ pd@(PdVar n τ as)
 = do n <- liftM F.intKvar fresh
      let s = (`F.RKvar` F.emptySubst) n
      addW $ WfCS γ' τ s
      return s
 where γ' = foldl' (++=) γ (map (\(τ, x, _) -> (x, ofType τ)) as) 
tySort (RVar _ (F.Reft(_, [a])))        = a
tySort (RConApp _ _ _ (F.Reft(_, [a]))) = a
tySort _                                = error "tySort"

-----------------------------------------------------------------------
---------- Helpers: Creating Refinement Types For Various Things ------
-----------------------------------------------------------------------

argExpr ::  CoreExpr -> Maybe F.Expr
argExpr (Var vy)         = Just $ F.EVar $ mkSymbol vy
argExpr (Lit c)          = Just $ snd $ literalConst c
argExpr (Tick _ e)		     = argExpr e
argExpr e                = errorstar $ "argExpr: " ++ (showPpr e)

varRefType γ x =  t 
  where t  = (γ ?= (mkSymbol x)) `strengthen` xr
        xr = F.symbolReft (mkSymbol x)

-----------------------------------------------------------------------
--------------- Forcing Strictness ------------------------------------
-----------------------------------------------------------------------

instance NFData Cinfo 

instance NFData CGEnv where
  rnf (CGE x1 x2 x3 x4 x5) 
    = x1 `seq` rnf x2 `seq` rnf x3  `seq` rnf x4

instance NFData SubC where
  rnf (SubC x1 x2 x3) 
    = rnf x1 `seq` rnf x2 `seq` rnf x3

instance NFData WfC where
  rnf (WfC x1 x2)   
    = rnf x1 `seq` rnf x2
  rnf (WfCS x1 _ x2)   
    = rnf x1 `seq` rnf x2



instance NFData CGInfo where
  rnf (CGInfo x1 x2 x3 x4 x5 x6 x7 x8) 
    = ({-# SCC "CGIrnf1" #-} rnf x1) `seq` 
      ({-# SCC "CGIrnf2" #-} rnf x2) `seq` 
      ({-# SCC "CGIrnf3" #-} rnf x3) `seq` 
      ({-# SCC "CGIrnf4" #-} rnf x4) `seq` 
      ({-# SCC "CGIrnf5" #-} rnf x5) `seq` 
      ({-# SCC "CGIrnf6" #-} rnf x6) `seq`
      ({-# SCC "CGIrnf6" #-} rnf x7) 


-----------------------------------------------------------------------
--------------- Cleaner Signatures For Rec-bindings -------------------
-----------------------------------------------------------------------

exprRefType :: CoreExpr -> RefType
exprRefType = exprRefType_ M.empty 

exprRefType_ :: M.Map Var RefType -> CoreExpr -> RefType 
exprRefType_ γ (Let b e) 
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAll (rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e) 
  = RFun (RB (mkSymbol x)) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x) 
  = M.findWithDefault (ofType $ varType x) x γ

exprRefType_ γ e
  = ofType $ exprType e

bindRefType_ γ (Rec xes)
  = extendγ γ [(x, exprRefType_ γ e) | (x,e) <- xes]

bindRefType_ γ (NonRec x e)
  = extendγ γ [(x, exprRefType_ γ e)]

extendγ γ xts
  = foldr (\(x,t) m -> M.insert x t m) γ xts

replaceSort :: (F.Refa, F.Refa) -> RefType -> RefType
replaceSort kp = fmap $ F.replaceSort kp 
replaceSorts :: (F.Refa, F.Reft) -> RefType -> RefType
replaceSorts pk = fmap $  F.replaceSorts pk

