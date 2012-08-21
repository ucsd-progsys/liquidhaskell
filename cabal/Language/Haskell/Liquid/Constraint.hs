{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}

{- Representation of Sub and WF Constraints, 
 - and code for syntax-directed constraint generation. -}

module Language.Haskell.Liquid.Constraint (
    generateConstraints
  , CGInfo (..)
  , kvars, kvars' -- symbols  -- debugging purposes
  ) where

import CoreSyn
import Literal          (literalType)
import Id               (idType, isDataConId_maybe)
import SrcLoc           
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
import Data.Monoid              (mconcat)
import Data.Maybe (isJust, maybeToList, fromJust, fromMaybe)
import qualified Data.Map as M
import Data.Bifunctor
import Data.List (inits, find, foldl')
import qualified Data.Set as S
import Text.Printf

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.Fixpoint         (PVar(..))
import Language.Haskell.Liquid.GhcInterface 
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType hiding  (splitArgsRes)
import Language.Haskell.Liquid.Predicates
import Language.Haskell.Liquid.GhcMisc          (tickSrcSpan, tvId)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Qualifier        
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data
import Control.DeepSeq

-----------------------------------------------------------------------
------------- Constraint Generation: Toplevel -------------------------
-----------------------------------------------------------------------

-- consGrty γ (x, t) 
--   =  addC (SubC γ' xt t) ("consGrty: upperBound " ++ xs)  
--   >> addC (SubC γ' t xt) ("consGrty: lowerBound " ++ xs) 
--   where γ' = γ `setLoc` (getSrcSpan x) 
--         xt = γ ?= (mkSymbol x)
--         xs = showPpr x

-- consAct info penv
--   = do γ   <- initEnv info penv
--        γ1  <- foldM consCB γ $ cbs info
--        tyi <- liftM tyConInfo get 
--        let grty' = mapSnd (addTyConInfo tyi) <$> grty info  
--        forM_ grty' (consGrty γ1)

consAct info penv
  = do γ <- initEnv info penv
       foldM consCB γ (cbs info)

generateConstraints :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} st { fixCs = fcs} { fixWfs = fws } { globals = gs }
  where st  = execState act $ initCGI info 
        act = consAct (info {cbs = fst pds}) (snd pds)
        fcs = concatMap splitC $ hsCs  st 
        fws = concatMap splitW $ hsWfs st
        gs  = F.fromListSEnv . map (mapSnd refTypeSortedReft) $ meas spc 
        pds = generatePredicates info
        spc = spec info


kvars :: (Data a) => a -> S.Set F.Symbol
kvars = everything S.union (S.empty `mkQ` grabKvar)
  where grabKvar (F.RKvar k _:: F.Refa) = S.singleton k
        grabKvar _                      = S.empty


kvars' :: (Data a) => a -> Int
kvars' = everything (plus') (0 `mkQ` grabKvar)
  where grabKvar (F.RKvar k _ :: F.Refa) = 1 
        grabKvar _                       = 0
        plus' !x !y                      = x + y 


initEnv :: GhcInfo -> F.SEnv PrType -> CG CGEnv  
initEnv info penv
  = do defaults <- forM (impVars info) $ \x -> liftM (x,) (trueTy $ varType x)
       tyi      <- tyConInfo <$> get 
       let f0    = grty info          -- asserted refinements     (for defined vars)
       let f1    = defaults           -- default TOP reftype      (for all vars) 
       let f2    = assm info          -- assumed refinements      (for imported vars)
       let f3    = ctor $ spec info   -- constructor refinements  (for measures) 
       let bs    = (map (unifyts' tyi penv)) <$> [f0, f1, f2, f3]
       let γ0    = measEnv (spec info) penv (head bs)
       return    $ foldl' (++=) γ0 [("initEnv", x, y) | (x, y) <- concat bs] 

unifyts' tyi penv = (second (addTyConInfo tyi)) . (unifyts penv)

unifyts penv (x, t) = (x', unify pt t)
 where pt = F.lookupSEnv x' penv
       x' = mkSymbol x

measEnv sp penv xts 
  = CGE { loc   = noSrcSpan
        , renv  = fromListREnv $ meas sp 
        , penv  = penv 
        , fenv  = F.fromListSEnv $ second refTypeSortedReft <$> meas sp 
        , recs  = S.empty 
        , invs  = mkRTyConInv $ invariants sp
        , grtys = fromListREnv xts 
        } 

assm = {- traceShow ("****** assm *****\n") . -} assm_grty impVars 
grty = {- traceShow ("****** grty *****\n") . -} assm_grty defVars

assm_grty f info = [ (x, mapReft ureft t) | (x, t) <- sigs, x `S.member` xs ] 
  where xs   = S.fromList $ f info 
        sigs = tySigs $ spec info  


-------------------------------------------------------------------
-------- Helpers: Reading/Extending Environment Bindings ----------
-------------------------------------------------------------------

data CGEnv 
  = CGE { loc   :: !SrcSpan          -- where in orig src
        , renv  :: !REnv             -- bindings in scope
        , penv  :: !(F.SEnv PrType)  -- bindings in scope
        , fenv  :: !F.FEnv           -- the fixpoint environment 
        , recs  :: !(S.Set Var)      -- recursive defs being processed (for annotations)
        , invs  :: !RTyConInv        -- datatype invariants 
        , grtys :: !REnv             -- top-level variables with (assert)-guarantees
        } deriving (Data, Typeable)

instance Outputable CGEnv where
  ppr = ppr . renv

instance Show CGEnv where
  show = showPpr

{- see tests/pos/polyfun for why you need everything in fixenv -} 
(++=) :: CGEnv-> (String, F.Symbol, RefType) -> CGEnv
γ ++= (msg, x, r') 
  | isBase r 
  = γ' { fenv = F.insertSEnv x (refTypeSortedReft r) (fenv γ) }
  | otherwise
  = γ' { fenv = insertFEnvClass r (fenv γ) }
  where γ' = γ { renv = insertREnv x r (renv γ) }  
        r  = normalize γ r'  

normalize γ = addRTyConInv (invs γ) . normalizePds
  
-- (+=) :: (CGEnv, String) -> (F.Symbol, RefType) -> CGEnv
(γ, msg) += (x, r)
  | x == F.dummySymbol
  = γ
  | x `memberREnv` (renv γ)
  = errorstar $ "ERROR: " ++ msg ++ " Duplicate Binding for " ++ F.symbolString x -- ++ " in REnv!\n\n" ++ show γ
  | otherwise
  =  γ ++= (msg, x, r) 

γ -= x 
  =  γ { renv = deleteREnv x (renv γ) } { fenv = F.deleteSEnv x (fenv γ) }

(?=) ::  CGEnv -> F.Symbol -> RefType 
γ ?= x
  = case lookupREnv x (renv γ) of
      Just t  -> t
      Nothing -> errorstar $ "EnvLookup: unknown = " ++ showPpr x

getPrType :: CGEnv -> F.Symbol -> Maybe PrType
getPrType γ x = F.lookupSEnv x (penv γ)

setLoc :: CGEnv -> SrcSpan -> CGEnv
γ `setLoc` src 
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
  where f ((RCls c ts) :: RefType) = [(c, ts)]
        f _                        = []

getTyVars = everything (++) ([] `mkQ` f)
  where f ((RVar (RV (α')) _) :: RefType) = [α'] 
        f _                               = []
 
-- isBase :: RType a -> Bool
isBase (RVar _ _)     = True
isBase (RApp _ _ _ _) = True
isBase _              = False

insertFEnvClass :: RefType -> F.FEnv -> F.FEnv
insertFEnvClass (RCls c ts) fenv
  | isNumericClass c
  = foldl' (\env x -> F.insertSEnv x numReft env) fenv numVars
  where numReft = F.trueSortedReft F.FNum
        numVars = [rTyVarSymbol a | (RVar a _) <- ts]
insertFEnvClass _ fenv 
  = fenv

rTyVarSymbol (RV (RTV α)) = typeUniqueSymbol $ TyVarTy α
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
  ppr c = ppr (senv c) <> blankLine 
          $+$ ((text " |- ") <+>   ( (ppr (lhs c)) 
                                  $+$ text "<:" 
                                  $+$ (ppr (rhs c))))
          $+$ blankLine
          $+$ blankLine

instance Outputable WfC where
  ppr (WfC w r)    = ppr w <> blankLine <> text " |- " <> ppr r <> blankLine <> blankLine 
  ppr (WfCS w τ s) = ppr w <> blankLine <> text " |- " <> braces (ppr τ <+> colon  <+> ppr s)

instance Outputable Cinfo where
  ppr (Ci src) = ppr src

--instance Outputable a => Outputable (F.SubC a) where
--  -- ppr (F.SubC {F.sinfo = s}) = text "Liquid Type Error: " <> ppr s
--  ppr
--instance Outputable a => Outputable (F.WfC a) where
--  ppr (F.SubC {F.sinfo = s}) = text "Liquid Type Error: " <> ppr s

------------------------------------------------------------
------------------- Constraint Splitting -------------------
------------------------------------------------------------

splitW ::  WfC -> [FixWfC]

splitW (WfC γ t@(RFun (RB x) t1 t2 _)) 
  =  bsplitW γ t
  ++ splitW (WfC γ t1) 
  ++ splitW (WfC ((γ, "splitW") += (x, t1)) t2)

splitW (WfC γ (RAll a r)) 
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ r))
  =  bsplitW γ t 

splitW (WfC γ (RCls _ _))
  = []

splitW (WfC γ t@(RApp c ts rs _))
  =  bsplitW γ t 
  ++ (concatMap splitW (map (WfC γ) ts)) 
  ++ (concatMap (rsplitW γ) (safeZip "splitW" rs ps))
 where ps = rTyConPs c


splitW (WfC _ t) 
  = [] -- errorstar $ "splitW cannot handle: " ++ showPpr t

-- bsplitW :: CGEnv -> RefType -> [FixWfC]
bsplitW γ t 
  | F.isNonTrivialSortedReft r'
  = [F.WfC env' r' Nothing ci] 
  | otherwise
  = []
  where env' = fenv γ
        r'   = refTypeSortedReft t
        ci   = Ci (loc γ)

-- rsplitW :: CGEnv -> (F.Reft, Predicate) -> [FixWfC]
rsplitW γ (RMono r, ((PV _ t as)))
  = [F.WfC env' r' Nothing ci]
  where env' = fenv γ'
        ci   = Ci (loc γ)
        r'   = refTypePredSortedReft (r, t)
        γ'   = foldl' (++=) γ (map (\(τ, x, _) -> ("rsplitW1", x, ofType τ)) as) 

rsplitW γ (RPoly t0, (PV _ t as))
  = splitW (WfC γ' t0)
  where γ'   = foldl' (++=) γ (map (\(τ, x, _) -> ("rsplitW2", x, ofType τ)) as) 

------------------------------------------------------------
splitC :: SubC -> [FixSubC]
------------------------------------------------------------

splitC (SubC γ t1@(RFun (RB x1) r1 r1' re1) t2@(RFun (RB x2) r2 r2' re2)) 
  =  bsplitC γ t1 t2 
  ++ splitC  (SubC γ r2 r1) 
  ++ splitC  (SubC γ' r1x2' r2') 
     where r1x2' = r1' `F.subst1` (x1, F.EVar x2) 
           γ'    = (γ, "splitC") += (x2, r2) 


splitC (SubC γ (RAll b1 t1) (RAll b2 t2))
  | b1 == b2
  = splitC $ SubC γ t1 t2

splitC (SubC γ (RAll (RV α1) t1) (RAll (RV α2) t2))
  = splitC $ SubC γ t1 t2' 
  where t2' = subsTyVar_meet' (α2, RVar (RV α1) top) t2


splitC c@(SubC γ (RAll _ _) (RAll _ _)) 
  = errorstar $ "splitc unexpected: " ++ showPpr c

{-
splitC (SubC γ t1 (RAll ((RP p@(PV _ τ _))) t2))
--  = splitC (SubC γ t1 (fmap (F.removeRPVar p) t2))
  = splitC (SubC γ t1 (replacePred (p, RPoly (ofType τ)) t2))
-}

splitC (SubC γ t1@(RApp c t1s r1s _) t2@(RApp c' t2s r2s _))
	= bsplitC γ t1 t2 
   ++ (concatMap splitC (zipWith (SubC γ) t1s t2s)) 
   ++ (concatMap (rsplitC γ) (rsplits r1s r2s (rTyConPs c')))

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _)) 
  | a1 == a2
  = bsplitC γ t1 t2

splitC (SubC _ (RCls c1 _) (RCls c2 _)) -- | c1 == c2
  = []

splitC (SubC _ t1 t2) 
  = []

chkTyConIds (RTyCon _ ps1) (RTyCon _ ps2) 
 = length ps1 == length ps2
  
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


rsplits [] _ _      = []
rsplits _ [] _      = []
rsplits _ _ []      = []
rsplits r1s r2s ps  = safeZip "rsplits1" (safeZip "rsplits2" r1s r2s) ps

rsplitC γ ((RMono r1, RMono r2), (PV _ t as))
  = [F.SubC env' F.PTrue r1' r2' Nothing [] ci]
  where env' = fenv γ'
        ci   = Ci (loc γ)
        r1'  = refTypePredSortedReft (r1, t)
        r2'  = refTypePredSortedReft (r2, t)
        γ'   = foldl' (++=) γ (map (\(τ, x, _) -> ("rsplitC1", x, ofType τ)) as) 
rsplitC γ ((RPoly r1, RPoly r2), PV _ t as)
  = splitC (SubC γ' r1 r2)
  where γ'   = foldl' (++=) γ (map (\(τ, x, _) -> ("rsplitC2", x, ofType τ)) as) 
rsplitC γ ((RPoly t, RMono r), p)  = error "rplit Rpoly - RMono"
{-  = case stripRTypeBase t of 
     Just x  -> rsplitC γ ((RMono x, (RMono r)), p)
     Nothing -> error "rsplitStrip" 
rsplitC γ ((RMono r, RPoly t), p) 
  = rsplitC γ ((RPoly ((ofType (ptype p)) `strengthen` r), (RPoly t)), p)
-}
-----------------------------------------------------------
-------------------- Generation: Types --------------------
-----------------------------------------------------------

newtype CGSpec = CGSpec (Ms.Spec F.Sort DataCon)

data CGInfo = CGInfo { hsCs       :: ![SubC]
                     , hsWfs      :: ![WfC]
                     , fixCs      :: ![FixSubC]
                     , fixWfs     :: ![FixWfC]
                     , globals    :: !F.FEnv
                     , freshIndex :: !Integer 
                     , annotMap   :: !(AnnInfo Annot) 
                     , tyConInfo  :: !(M.Map TC.TyCon RTyCon) 
                     , specQuals  :: ![Qualifier]
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

initCGI info = CGInfo { 
    hsCs       = [] 
  , hsWfs      = [] 
  , fixCs      = []
  , fixWfs     = [] 
  , globals    = F.emptySEnv
  , freshIndex = 0
  , annotMap   = AI M.empty
  , tyConInfo  = makeTyConInfo $ tconsP $ spec info 
  , specQuals  = specificationQualifiers info
  }

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "


addC :: SubC -> String -> CG ()  
addC !c@(SubC _ t1 t2) msg 
  = -- trace ("addC " ++ show t1 ++ "\n < \n" ++ show t2 ++ msg) $  
    modify $ \s -> s { hsCs  = c : (hsCs s) }

addW   :: WfC -> CG ()  
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

-- Used for annotation binders (i.e. at binder sites)
addIdA :: Var -> Annot -> CG ()
addIdA !x !t  = modify $ \s -> s { annotMap = addA (getSrcSpan x) (Just x) t $ annotMap s } 

-- Used for annotating reads (i.e. at Var x sites) 
addLocA :: Maybe Var -> SrcSpan -> Annot -> CG ()
addLocA !xo !l !t 
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }

addA !l !xo@(Just _)  !t !a@(AI m) 
  | isGoodSrcSpan l -- && not (l `M.member` m)
  = AI $ M.insert l (xo, t) m
addA !l !xo@(Nothing) !t !a@(AI m) 
  | l `M.member` m  -- only spans known to be variables
  = AI $ M.insert l (xo, t) m
addA _ _ _ !a 
  = a

--addA !l !xo !t !a@(AI m) 
--  | isGoodSrcSpan l -- && not (l `M.member` m)
--  = AI $ M.insert l (xo, t) m
--  | otherwise
--  = a

-------------------------------------------------------------------
------------------------ Generation: Freshness --------------------
-------------------------------------------------------------------

-- To revert to the old setup, just do
-- freshTy_pretty = freshTy
freshTy_pretty e τ = refresh $ {-traceShow ("exprRefType: " ++ showPpr e) $-} exprRefType e

freshTy' _ = refresh . ofType 

freshTy :: CoreExpr -> Type -> CG RefType
freshTy = freshTy' 

trueTy  :: Type -> CG RefType
trueTy t 
  = do t   <- true $ ofType t
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

instance Freshable (F.Refa) where
  fresh = liftM (`F.RKvar` F.emptySubst) freshK
    where freshK = liftM F.intKvar fresh

instance Freshable [F.Refa] where
  fresh = liftM single fresh

instance Freshable (F.Reft) where
  fresh = errorstar "fresh Reft"
  true    (F.Reft (v, _)) = return $ F.Reft (v, []) 
  refresh (F.Reft (v, _)) = liftM (F.Reft . (v, )) fresh

instance Freshable RefType where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

trueRefType (RAll α t)       
  = liftM (RAll α) (true t)
trueRefType (RFun _ t t' _)    
  = liftM3 rFun fresh (true t) (true t')
trueRefType (RApp c ts refs _)  
  = liftM (\ts -> RApp c ts truerefs (F.trueReft)) (mapM true ts)
		where truerefs = (RPoly . ofType . ptype) <$> (rTyConPs c)
trueRefType t                
  = return t

refreshRefType (RAll α t)       
  = liftM (RAll α) (refresh t)
refreshRefType (RFun b t t' _)
  | b == (RB F.dummySymbol)
  = liftM3 rFun fresh (refresh t) (refresh t')
  | otherwise
  = liftM2 (rFun b) (refresh t) (refresh t')
refreshRefType (RApp rc ts _ r)  
  = do tyi                 <- tyConInfo <$> get
       let RApp rc' _ rs _  = expandRApp tyi (RApp rc ts [] r)
       liftM3 (RApp rc') (mapM refresh ts) (mapM refreshRef rs) (refresh r)
refreshRefType (RVar a r)  
  = liftM (RVar a) (refresh r)
refreshRefType t                
  = return t

refreshRef (RPoly t) = RPoly <$> (refreshRefType t)
refreshRef (RMono r) = error "refreshRef: unexpected"

isBaseTyCon c
  | c == intTyCon 
  = True
  | c == boolTyCon
  = True
  | otherwise
  = False

addTyConInfo = mapBot . expandRApp

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------

consCB :: CGEnv -> CoreBind -> CG CGEnv 

-- OLD
-- consCB γ b@(NonRec x e)
--   = do t <- unify pt <$> consE γ e
--        addIdA x (Left t)
--        return $  γ ++= ("consCB2", x', t)
--     where x' = mkSymbol x
--           pt = getPrType γ x'
--           
-- consCB γ (Rec xes) 
--   = do rts   <- mapM (\e -> freshTy_pretty e $ exprType e) es
--        let ts = zipWith unify pts rts 
--        let γ' = foldl' (\γ z -> (γ, "consCB1") += z) (γ `withRecs` xs) (zip vs ts)
--        zipWithM_ (cconsE γ') es  ts
--        zipWithM_ addIdA xs (Left <$> ts)
--        mapM_     addW (WfC γ <$> rts)
--        return γ'
--    where (xs, es) = unzip xes
--          vs       = mkSymbol    <$> xs
--          pts      = getPrType γ <$> vs

-- NEW
consCB γ (Rec xes) 
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       let xts = [(x, to) | (x, _, to) <- xets, not (isGrty x)]
       let γ'  =  foldl' extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind γ') xets
       return γ' 
    where isGrty x = (mkSymbol x) `memberREnv` (grtys γ)

consCB γ b@(NonRec x e)
  = do to  <- varTemplate γ (x, Nothing) 
       to' <- consBind γ (x, e, to)
       return $ extender γ (x, to')

extender γ (x, Just t) = γ ++= ("extender", mkSymbol x, t)
extender γ _           = γ

consBind γ (x, e, Just t) 
  = do cconsE γ e t
       addIdA x (Left t)
       return Nothing 

consBind γ (x, e, Nothing) 
   = do t <- unifyVar γ x <$> consE γ e
        addIdA x (Left t)
        return $ Just t

varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Maybe RefType)
varTemplate γ (x, eo)
  = case (eo, lookupREnv (mkSymbol x) (grtys γ)) of
      (_, Just t) -> return $ Just t
      (Just e, _) -> do t <- unifyVar γ x <$> freshTy_pretty e (exprType e)
                        addW (WfC γ t)
                        return $ Just t
      (_,      _) -> return Nothing

unifyVar γ x rt = unify (getPrType γ (mkSymbol x)) rt


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
       forM_ cases $ cconsCase γ' x t nonDefAlts 
    where nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]

cconsE γ (Lam α e) (RAll (RV α') t) | isTyVar α 
  = cconsE γ e $ subsTyVar_meet' (α', rVar α top) t 

cconsE γ (Lam x e) (RFun (RB y) ty t _) 
  | not (isTyVar x) 
  = do cconsE ((γ, "cconsE") += (mkSymbol x, ty)) e te 
       addIdA x (Left ty) 
    where te = t `F.subst1` (y, F.EVar $ mkSymbol x)

cconsE γ (Tick tt e) t   
  = cconsE (γ `setLoc` tt') e t
    where tt' = {- traceShow ("tickSrcSpan: e = " ++ showPpr e) $ -} tickSrcSpan tt

cconsE γ (Cast e _) t     
  = cconsE γ e t 

cconsE γ e (RAll (RP p@(PV _ τ _)) t)
  = do s <- truePredRef p
       cconsE γ e (replacePred "cconsE" (p, RPoly s) t)

cconsE γ e t
  = do te <- consE γ e
       addC (SubC γ te t) ("cconsE" ++ showPpr e)


-------------------------------------------------------------------
consE :: CGEnv -> Expr Var -> CG RefType 
-------------------------------------------------------------------

consE γ (Var x)   
  = do addLocA (Just x) (loc γ) (varAnn γ x t)
       return t
    where t = varRefType γ x

consE _ (Lit c) 
  = return $ literalRefType c

consE γ (App e (Type τ)) 
  = do RAll (RV α) te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       t              <- if isGeneric α te then freshTy e τ else trueTy τ
       addW            $ WfC γ t
       return          $ subsTyVar_meet' (α, t) te

consE γ e'@(App e a) | eqType (exprType a) predType 
  = do t0 <- consE γ e
       case t0 of
         RAll (RP p) t -> do s <- freshPredRef γ e' p
                             return $ replacePred "consE" (p, RPoly s) t 
         _             -> return t0

consE γ e'@(App e a)               
  = do RFun (RB x) tx t _ <- liftM (checkFun ("Non-fun App with caller", e)) $ consE γ e 
       cconsE γ a tx 
       case argExpr a of 
         Just e  -> return $ t `F.subst1` (x, e)
         Nothing -> errorstar $ "consE: App crashes on" ++ showPpr a 

consE γ (Lam α e) | isTyVar α 
  = liftM (RAll (rTyVar α)) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy (Var x) τx 
       t1     <- consE ((γ, "consE") += (mkSymbol x, tx)) e1
       addIdA x (Left tx) 
       addW   $ WfC γ tx 
       return $ rFun (RB (mkSymbol x)) tx t1
    where FunTy τx _ = exprType e 

consE γ e@(Let _ _)       
  = cconsFreshE γ e

consE γ e@(Case _ _ _ _) 
  = cconsFreshE γ e

consE γ (Tick tt e)
  = do t <- consE (γ `setLoc` l) e
       addLocA Nothing l (Left t)
       return t
    where l = {- traceShow ("tickSrcSpan: e = " ++ showPpr e) $ -} tickSrcSpan tt


consE γ (Cast e _)      
  = consE γ e 

consE env e	    
  = errorstar $ "consE cannot handle " ++ showPpr e

cconsFreshE γ e
  = do t   <- freshTy e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

cconsCase :: CGEnv -> Var -> RefType -> [AltCon] -> (AltCon, [Var], CoreExpr) -> CG ()

cconsCase γ x t _ (DataAlt c, ys, ce) 
 = do yts'            <- mkyts γ ys yts
      let cbs          = zip (x':ys') (xt:yts')
      let cγ           = addBinders γ x' cbs
      cconsE cγ ce t
 where (x':ys')        = mkSymbol <$> (x:ys)
       xt0             = checkTyCon x $ γ ?= x'
       tdc             = γ ?= (dataConSymbol c)
       (rtd, yts, xt') = unfoldR tdc xt0 ys'
       r1              = dataConReft   c   ys' 
       r2              = dataConMsReft rtd ys'
       xt              = xt0 `strengthen` (r1 `meet` r2)

cconsCase γ x t acs (a, _, ce) 
  = cconsE cγ ce t
  where cγ  = addBinders γ x' [(x', xt')]
        x'  = mkSymbol x
        xt' = altRefType (γ ?= x') acs a 

altRefType t _   (LitAlt l) 
  = -- t `meet` (literalRefType l)
    t `strengthen` literalReft l

altRefType t acs DEFAULT    
  = t `strengthen` (mconcat [notLiteralReft l | LitAlt l <- acs])
          
notLiteralReft =  F.notExprReft . snd . literalConst 

mkyts γ ys yts 
  = liftM (reverse . snd) $ foldM mkyt (γ, []) $ zip ys yts
mkyt (γ, ts) (y, yt)
  = do t' <- freshTy (Var y) (toType yt)
       addC (SubC γ yt t') "mkyts"
       addW (WfC γ t') 
       return (γ ++= ("mkyt", mkSymbol y, t'), t':ts) 

unfoldR td t0@(RApp tc ts rs _) ys = (t3, yts, rt)
  where (vs, ps, t0) = rsplitVsPs td
        t1 = foldl' (flip subsTyVar_meet') t0 (zip vs ts)
        t2 = foldl' (flip (replacePred "unfoldR" )) t1 (safeZip "unfoldR" (reverse ps) rs)
        (ys0, yts', rt) =  rsplitArgsRes t2
        (t3:yts) = F.subst su <$> (t2:yts')
        su  = F.mkSubst [(x, F.EVar y)| (x, y)<- zip ys0 ys]

takeReft c (RApp _ _ _ a) 
  | c == nilDataCon || c == consDataCon
  = a
  | otherwise
		= F.trueReft
takeReft _ _                
  = F.trueReft

instance Show CoreExpr where
  show = showSDoc . ppr

addBinders γ0 x' cbs 
  = foldl' (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]
    -- where wr γ (x, t) = γ ++= ("addBinders", x, t) 

checkTyCon _ t@(RApp _ _ _ _) = t
checkTyCon x t                = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkRPred _ t@(RAll _ _)     = t
checkRPred x t                = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkFun _ t@(RFun _ _ _ _)   = t
checkFun x t                  = errorstar $ showPpr x ++ "type: " ++ showPpr t

checkAll _ t@(RAll _ _)       = t
checkAll x t                  = errorstar $ showPpr x ++ "type: " ++ showPpr t

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

-----------------------------------------------------------------------
---------- Helpers: Creating Fresh Refinement ------------------ ------
-----------------------------------------------------------------------

truePredRef pd@(PV n τ as)
  = trueTy τ

freshPredRef γ e pd@(PV n τ as)
  = do t <- freshTy e τ
       addW $ WfC γ' t
       return t
  where γ' = foldl' (++=) γ (map (\(τ, x, _) -> ("freshPredRef", x, ofType τ)) as) 

tySort (RVar _ (F.Reft(_, [a])))     = a
tySort (RApp _ _ _ (F.Reft(_, [a]))) = a
tySort _                             = error "tySort"

-----------------------------------------------------------------------
---------- Helpers: Creating Refinement Types For Various Things ------
-----------------------------------------------------------------------

argExpr ::  CoreExpr -> Maybe F.Expr
argExpr (Var vy)         = Just $ F.EVar $ mkSymbol vy
argExpr (Lit c)          = Just $ snd $ literalConst c
argExpr (Tick _ e)		 = argExpr e
argExpr e                = errorstar $ "argExpr: " ++ (showPpr e)

varRefType γ x =  t 
  where t  = (γ ?= (mkSymbol x)) `strengthen` xr
        xr = F.symbolReft (mkSymbol x)

-- GENSUB: subsTyVar_meet' (α, t) = subsTyVar_meet (α, t) 
subsTyVar_meet' (α, t) = subsTyVar_meet (α, toType t, t)

-----------------------------------------------------------------------
--------------- Forcing Strictness ------------------------------------
-----------------------------------------------------------------------

instance NFData Cinfo 

instance NFData CGEnv where
  rnf (CGE x1 x2 x3 x4 x5 x6 x7) 
    = x1 `seq` rnf x2 `seq` x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6  `seq` x7 `seq` ()

instance NFData SubC where
  rnf (SubC x1 x2 x3) 
    = rnf x1 `seq` rnf x2 `seq` rnf x3

instance NFData Class where
  rnf _ = ()

instance NFData RTyCon where
  rnf _ = ()

instance NFData Type where 
  rnf _ = ()

instance NFData WfC where
  rnf (WfC x1 x2)   
    = rnf x1 `seq` rnf x2
  rnf (WfCS x1 _ x2)   
    = rnf x1 `seq` rnf x2

instance NFData CGInfo where
  rnf (CGInfo x1 x2 x3 x4 x5 x6 x7 x8 x9) 
    = ({-# SCC "CGIrnf1" #-} rnf x1) `seq` 
      ({-# SCC "CGIrnf2" #-} rnf x2) `seq` 
      ({-# SCC "CGIrnf3" #-} rnf x3) `seq` 
      ({-# SCC "CGIrnf4" #-} rnf x4) `seq` 
      ({-# SCC "CGIrnf5" #-} rnf x5) `seq` 
      ({-# SCC "CGIrnf6" #-} rnf x6) `seq`
      ({-# SCC "CGIrnf7" #-} rnf x7) `seq`
      ({-# SCC "CGIrnf8" #-} rnf x9) 

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
  = rFun (RB (mkSymbol x)) (ofType $ varType x) (exprRefType_ γ e)

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

-------------------------------------------------------------------
----------- Data TyCon Invariants ---------------------------------
-------------------------------------------------------------------

type RTyConInv = M.Map RTyCon F.Reft

addRTyConInv :: RTyConInv -> RefType -> RefType
addRTyConInv m t@(RApp c _ _ _) 
  = fromMaybe t (strengthen t <$> M.lookup c m)
addRTyConInv _ t 
  = t 

mkRTyConInv    :: [SpecType] -> RTyConInv 
mkRTyConInv ts = mconcat <$> group [ (c, r) | RApp c _ _ (U r _) <- strip <$> ts]
                 where strip (RAll _ t) = strip t
                       strip t          = t
