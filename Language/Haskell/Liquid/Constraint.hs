{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, DeriveDataTypeable, BangPatterns #-}

-- | This module defines the representation of Subtyping and WF Constraints, and 
-- the code for syntax-directed constraint generation. 

module Language.Haskell.Liquid.Constraint (
    
    -- * Constraint information output by generator 
    CGInfo (..)

    -- * Function that does the actual generation
  , generateConstraints

  -- * KVars in constraints, for debug purposes
  -- , kvars, kvars'
  ) where

import CoreSyn
import SrcLoc           
import Type             -- (coreEqType)
import PrelNames
import qualified TyCon as TC

import TypeRep 
import Class            (Class, className)
import PrelInfo         (isNumericClass)
import Var
import Name             (getSrcSpan)
import Outputable   hiding (empty)
import Control.Monad.State

import Control.Exception.Base
import Control.Applicative      ((<$>))
import Data.Monoid              (mconcat)
import Data.Maybe (fromMaybe)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import Data.Bifunctor
import Data.List (foldl')

import qualified Language.Haskell.Liquid.CTags      as Tg
import qualified Language.Haskell.Liquid.Fixpoint   as F
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.Annotate
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType         hiding (freeTyVars) 
import Language.Haskell.Liquid.Predicates
import Language.Haskell.Liquid.GhcMisc          (tickSrcSpan)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Qualifier        
import Control.DeepSeq

-----------------------------------------------------------------------
------------- Constraint Generation: Toplevel -------------------------
-----------------------------------------------------------------------

generateConstraints :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI info
  where act = consAct (info {cbs = fst pds}) (snd pds)
        pds = generatePredicates info

consAct info penv
  = do γ   <- initEnv info penv
       foldM consCB γ (cbs info)
       -- st  <- get
       hcs <- hsCs  <$> get 
       hws <- hsWfs <$> get
       fcs <- concat <$> mapM splitC hcs -- (hsCs st)
       fws <- concat <$> mapM splitW hws -- (hsWfs st)
       modify $ \st -> st { fixCs = fcs } { fixWfs = fws }

initEnv :: GhcInfo -> F.SEnv PrType -> CG CGEnv  
initEnv info penv
  = do defaults <- forM (impVars info) $ \x -> liftM (x,) (trueTy $ varType x)
       tyi      <- tyConInfo <$> get 
       let f0    = grty info          -- asserted refinements     (for defined vars)
       let f1    = defaults           -- default TOP reftype      (for all vars) 
       let f2    = assm info          -- assumed refinements      (for imported vars)
       let f3    = ctor $ spec info   -- constructor refinements  (for measures) 
       let bs    = (map (unifyts' tyi penv)) <$> [f0, f1, f2, f3]
       let γ0    = measEnv (spec info) penv (head bs) (cbs info)
       foldM (++=) γ0 [("initEnv", x, y) | (x, y) <- concat bs]
       -- return    $ foldl' (++=) γ0 [("initEnv", x, y) | (x, y) <- concat bs] 

unifyts' tyi penv = (second (addTyConInfo tyi)) . (unifyts penv)

unifyts penv (x, t) = (x', unify pt t)
 where pt = F.lookupSEnv x' penv
       x' = varSymbol x

measEnv sp penv xts cbs
  = CGE { loc   = noSrcSpan
        , renv  = fromListREnv   $ second uRType          <$> meas sp 
        , syenv = F.fromListSEnv $ freeSyms sp 
        , penv  = penv 
        , fenv  = F.emptyIBindEnv -- F.fromListSEnv $ second (rTypeSortedReft tce) <$> meas sp 
        , recs  = S.empty 
        , invs  = mkRTyConInv    $ invariants sp
        , grtys = fromListREnv xts 
        , emb   = tce 
        , tgEnv = Tg.makeTagEnv cbs
        , tgKey = Nothing
        } 
    where tce = tcEmbeds sp

assm = {- traceShow ("****** assm *****\n") . -} assm_grty impVars 
grty = {- traceShow ("****** grty *****\n") . -} assm_grty defVars

assm_grty f info = [ (x, {- toReft <$> -} t) | (x, t) <- sigs, x `S.member` xs ] 
  where xs   = S.fromList $ f info 
        sigs = tySigs $ spec info  


------------------------------------------------------------------------
-- | Helpers: Reading/Extending Environment Bindings -------------------
------------------------------------------------------------------------

data CGEnv 
  = CGE { loc    :: !SrcSpan           -- ^ Location in original source file
        , renv   :: !REnv              -- ^ SpecTypes for Bindings in scope
        , syenv  :: !(F.SEnv Var)      -- ^ Map from free Symbols (e.g. datacons) to Var
        , penv   :: !(F.SEnv PrType)   -- ^ PrTypes for top-level bindings (merge with renv) 
        , fenv   :: !F.IBindEnv        -- ^ Integer Keys for Fixpoint Environment
        , recs   :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
        , invs   :: !RTyConInv         -- ^ Datatype invariants 
        , grtys  :: !REnv              -- ^ Top-level variables with (assert)-guarantees to verify
        , emb    :: F.TCEmb TC.TyCon   -- ^ How to embed GHC Tycons into fixpoint sorts
        , tgEnv :: !Tg.TagEnv          -- ^ Map from top-level binders to fixpoint tag
        , tgKey :: !(Maybe Tg.TagKey)  -- ^ Current top-level binder
        } -- deriving (Data, Typeable)

instance Outputable CGEnv where
  ppr = ppr . renv

instance Show CGEnv where
  show = showPpr

getTag :: CGEnv -> F.Tag
getTag γ = maybe Tg.defaultTag (`Tg.getTag` (tgEnv γ)) (tgKey γ)

getPrType :: CGEnv -> F.Symbol -> Maybe PrType
getPrType γ x = F.lookupSEnv x (penv γ)

setLoc :: CGEnv -> SrcSpan -> CGEnv
γ `setLoc` src 
  | isGoodSrcSpan src = γ { loc = src } 
  | otherwise         = γ

withRecs :: CGEnv -> [Var] -> CGEnv 
withRecs γ xs  = γ { recs = foldl' (flip S.insert) (recs γ) xs }

setBind :: CGEnv -> Tg.TagKey -> CGEnv  
setBind γ k 
  | Tg.memTagEnv k (tgEnv γ) = γ { tgKey = Just k }
  | otherwise                = γ


isGeneric :: RTyVar -> SpecType -> Bool
isGeneric α t =  all (\(c, α') -> (α'/=α) || isOrd c || isEq c ) (classConstrs t)
  where classConstrs t = [(c, α') | (c, ts) <- tyClasses t
                                  , t'      <- ts
                                  , α'      <- freeTyVars t']
        isOrd          = (ordClassName ==) . className
        isEq           = (eqClassName ==) . className

-- isBase :: RType a -> Bool
isBase (RVar _ _)     = True
isBase (RApp _ _ _ _) = True
isBase _              = False


rTyVarSymbol (RTV α) = typeUniqueSymbol $ TyVarTy α

-----------------------------------------------------------------
------------------- Constraints: Types --------------------------
-----------------------------------------------------------------

newtype Cinfo = Ci SrcSpan deriving (Eq, Ord) -- , Data, Typeable)

data SubC     = SubC { senv  :: !CGEnv
                     , lhs   :: !SpecType
                     , rhs   :: !SpecType 
                     } -- deriving (Data, Typeable)

data WfC      = WfC  !CGEnv !SpecType 
              -- deriving (Data, Typeable)

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

splitW ::  WfC -> CG [FixWfC]

splitW (WfC γ t@(RFun x t1 t2 _)) 
  =  do let ws = bsplitW γ t
        ws'   <- splitW (WfC γ t1) 
        γ'    <- (γ, "splitW") += (x, t1)
        ws''  <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (RAllT _ r)) 
  = splitW (WfC γ r)

splitW (WfC γ (RAllP _ r)) 
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ _))
  = return $ bsplitW γ t 

splitW (WfC _ (RCls _ _))
  = return []

splitW (WfC γ t@(RApp c ts rs _))
  =  do let ws = bsplitW γ t 
        ws'   <- concat <$> mapM splitW (map (WfC γ) ts)
        ws''  <- concat <$> mapM (rsplitW γ) (safeZip "splitW" rs (rTyConPs c))
        return $ ws ++ ws' ++ ws''

splitW (WfC _ t) 
  = errorstar $ "splitW cannot handle: " ++ showPpr t

rsplitW γ (RMono r, ((PV _ t as)))
  = do γ'    <- foldM (++=) γ (map (\(τ, x, _) -> ("rsplitW1", x, ofRSort τ)) as) 
       let r' = mkSortedReft (emb γ) t $ toReft r
       return [F.WfC (fenv γ') r' Nothing (Ci (loc γ))]

rsplitW γ (RPoly t0, (PV _ _ as))
  = do γ'  <- foldM (++=) γ (map (\(τ, x, _) -> ("rsplitW2", x, ofRSort τ)) as) 
       splitW (WfC γ' t0)

bsplitW :: CGEnv -> SpecType -> [FixWfC]
bsplitW γ t 
  | F.isNonTrivialSortedReft r'
  = [F.WfC (fenv γ) r' Nothing ci] 
  | otherwise
  = []
  where r' = rTypeSortedReft (emb γ) t
        ci = (Ci (loc γ))

mkSortedReft tce = F.RR . rTypeSort tce

------------------------------------------------------------
splitC :: SubC -> CG [FixSubC]
------------------------------------------------------------

splitC (SubC γ (REx x tx t1) (REx x2 _ t2))
  = do γ' <- (γ, "addExBind 0") += (x, existentialRefType γ tx)
       assert (x == x2) $ splitC (SubC γ' t1 t2)

splitC (SubC γ (REx x tx t1) t2) 
  = do γ' <- (γ, "addExBind 1") += (x, existentialRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (REx x tx t2))
  = do γ' <- (γ, "addExBind 2") += (x, existentialRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1@(RFun x1 r1 r1' _) t2@(RFun x2 r2 r2' _)) 
  =  do let cs    = bsplitC γ t1 t2 
        cs'      <- splitC  (SubC γ r2 r1) 
        γ'       <- (γ, "splitC") += (x2, r2) 
        let r1x2' = r1' `F.subst1` (x1, F.EVar x2) 
        cs''     <- splitC  (SubC γ' r1x2' r2') 
        return    $ cs ++ cs' ++ cs''

splitC (SubC γ (RAllP p1 t1) (RAllP p2 t2))
  | p1 == p2
  = splitC $ SubC γ t1 t2

splitC (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2 
  = splitC $ SubC γ t1 t2
  | otherwise   
  = splitC $ SubC γ t1 t2' 
  where t2' = subsTyVar_meet' (α2, RVar α1 top) t2

splitC (SubC γ t1@(RApp c t1s r1s _) t2@(RApp c' t2s r2s _))
  = do let cs = bsplitC γ t1 t2
       cs'   <- concat <$> mapM splitC (zipWith (SubC γ) t1s t2s)
       cs''  <- concat <$> mapM (rsplitC γ) (rsplits r1s r2s' (rTyConPs c))
       return $ cs ++ cs' ++ cs''
    where r2s'    = F.subst su <$> r2s
          su      = F.mkSubst [(x, F.EVar y) | (x, y) <- zip pVars' pVars]
          pVars   = concatMap getVars (rTyConPs c)
          pVars'  = concatMap getVars (rTyConPs c')
          getVars = (snd3 <$>) . pargs

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _)) 
  | a1 == a2
  = return $ bsplitC γ t1 t2

splitC (SubC _ (RCls c1 _) (RCls c2 _)) | c1 == c2
  = return []

-- TODO: MASSIVE SOUNDNESS PROBLEM
-- splitC (SubC _ t1 t2) 
--   = []
splitC c@(SubC _ _ _) 
  = errorstar $ "(Another Broken Test!!!) splitc unexpected: " ++ showPpr c

bsplitC γ t1 t2 
  | F.isFunctionSortedReft r1' && F.isNonTrivialSortedReft r2'
  = [F.SubC γ' F.PTrue (r1' {F.sr_reft = top}) r2' Nothing tag ci]
  | F.isNonTrivialSortedReft r2'
  = [F.SubC γ' F.PTrue r1' r2' Nothing tag ci]
  | otherwise
  = []
  where γ'      = fenv γ
        r1'     = rTypeSortedReft (emb γ) t1
        r2'     = rTypeSortedReft (emb γ) t2
        ci      = Ci (loc γ)
        tag     = getTag γ

rsplits [] _ _      = []
rsplits _ [] _      = []
rsplits _ _ []      = []
rsplits r1s r2s ps  = safeZip "rsplits1" (safeZip "rsplits2" r1s r2s) ps

rsplitC γ ((RMono r1, RMono r2), (PV _ t as))
  = do let r1'  = mkSortedReft (emb γ) t (toReft r1)
       let r2'  = mkSortedReft (emb γ) t (toReft r2)
       γ'      <- foldM (++=) γ (map (\(τ, x, _) -> ("rsplitC1", x, ofRSort τ)) as) 
       return   $ [F.SubC (fenv γ') F.PTrue r1' r2' Nothing [] (Ci (loc γ))]

rsplitC γ ((RPoly r1, RPoly r2), PV _ _ as)
  = do γ'  <- foldM (++=) γ (map (\(τ, x, _) -> ("rsplitC2", x, ofRSort τ)) as) 
       splitC (SubC γ' r1 r2)

rsplitC _ _  
  = error "rsplit Rpoly - RMono"

-----------------------------------------------------------
-------------------- Generation: Types --------------------
-----------------------------------------------------------

data CGInfo = CGInfo { hsCs       :: ![SubC]
                     , hsWfs      :: ![WfC]
                     , fixCs      :: ![FixSubC]
                     , fixWfs     :: ![FixWfC]
                     , globals    :: !F.FEnv
                     , freshIndex :: !Integer 
                     , binds      :: !F.BindEnv 
                     , annotMap   :: !(AnnInfo Annot) 
                     , tyConInfo  :: !(M.HashMap TC.TyCon RTyCon) 
                     , specQuals  :: ![Qualifier]
                     , tyConEmbed :: !(F.TCEmb TC.TyCon)
                     , kuts       :: !(F.Kuts)
                     , lits       :: ![(F.Symbol, F.Sort)]
                     } -- deriving (Data, Typeable)

instance Outputable CGInfo where 
  ppr cgi =  {-# SCC "ppr_CGI" #-} ppr_CGInfo cgi

ppr_CGInfo cgi 
  =  (text "*********** Haskell SubConstraints ***********")
  $$ (ppr $ hsCs  cgi)
  $$ (text "*********** Haskell WFConstraints ************")
  $$ (ppr $ hsWfs cgi)
  $$ (text "*********** Fixpoint SubConstraints **********")
  $$ (ppr $ fixCs cgi)
  $$ (text "*********** Fixpoint WFConstraints ************")
  $$ (ppr $ fixWfs cgi)
  $$ (text "*********** Fixpoint Kut Variables ************")
  $$ (ppr $ kuts cgi)
  $$ (text "*********** Literals in Source     ************")
  $$ (ppr $ lits cgi)


type CG = State CGInfo

initCGI info = CGInfo { 
    hsCs       = [] 
  , hsWfs      = [] 
  , fixCs      = []
  , fixWfs     = [] 
  , globals    = F.fromListSEnv . map (mapSnd (rTypeSortedReft (tcEmbeds spc))) $ meas spc
  , freshIndex = 0
  , binds      = F.emptyBindEnv
  , annotMap   = AI M.empty
  , tyConInfo  = makeTyConInfo $ tconsP spc
  , specQuals  = specificationQualifiers info
  , tyConEmbed = tce  
  , kuts       = F.ksEmpty 
  , lits       = coreBindLits tce $ cbs info 
  } where tce  = tcEmbeds $ spec info
          spc  = spec info


coreBindLits tce cbs = sortNub [ (x, so) | (_, F.ELit x so) <- lconsts]
  where lconsts      = literalConst tce <$> literals cbs

{- see tests/pos/polyfun for why you need everything in fixenv -} 
(++=) :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
γ ++= (_, x, r') 
  = do let r  = normalize γ r'  
       let γ' = γ { renv = insertREnv x r (renv γ) }  
       is    <- if isBase r 
                  then liftM ( :[]) $ addBind x (rTypeSortedReft (emb γ) r) 
                  else addClassBind r
       return $ γ' { fenv = F.insertsIBindEnv is (fenv γ) }


normalize γ = addRTyConInv (invs γ) . normalizePds

(+=) :: (CGEnv, String) -> (F.Symbol, SpecType) -> CG CGEnv
(γ, msg) += (x, r)
  | x == F.dummySymbol
  = return γ
  | x `memberREnv` (renv γ)
  = err 
  | otherwise
  =  γ ++= (msg, x, r) 
  where err = errorstar $ msg ++ " Duplicate binding for " 
                              ++ F.symbolString x 
                              ++ "\n New: " ++ showPpr r
                              ++ "\n Old: " ++ showPpr (x `lookupREnv` (renv γ))
                        
γ -= x =  γ {renv = deleteREnv x (renv γ)}

(?=) ::  CGEnv -> F.Symbol -> SpecType 
γ ?= x = fromMaybe err $ lookupREnv x (renv γ)
         where err = errorstar $ "EnvLookup: unknown " 
                               ++ showPpr x 
                               ++ " in renv " 
                               ++ showPpr (renv γ)


addBind :: F.Symbol -> F.SortedReft -> CG F.BindId
addBind x r 
  = do st          <- get
       let (i, bs') = F.insertBindEnv x r (binds st)
       put          $ st { binds = bs' }
       return i -- traceShow ("addBind: " ++ showPpr x) i

addClassBind :: SpecType -> CG [F.BindId] -- F.FEnv -> F.FEnv
addClassBind (RCls c ts)
  | isNumericClass c
  = do let numReft = F.trueSortedReft F.FNum
       let numVars = [rTyVarSymbol a | (RVar a _) <- ts]
       is         <- forM numVars (`addBind` numReft)
       return is
addClassBind _ 
  = return [] 


addSpecC :: SubC -> CG ()  

addSpecC (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2 
  = addSpecC $ SubC γ t1 t2
  | otherwise   
  = addSpecC $ SubC γ t1 t2' 
  where t2' = subsTyVar_meet' (α2, RVar α1 top) t2

addSpecC (SubC γ t spect)
  = do addLits (pVartoLit embγ <$> πs)
       addC (SubC γ t spect') "addSpecC"
  where spect' = mkUnivs as [] (fmap (replacePredsWithRefs su) tbody)
        (as, πs, tbody) = bkUniv spect
        su = M.fromList [(uPVar p, pVartoRConc embγ p) | p <- πs]
        embγ = emb γ

addC :: SubC -> String -> CG ()  
addC !c@(SubC _ _ _) _ 
  = -- trace ("addC " ++ show t1 ++ "\n < \n" ++ show t2 ++ msg) $  
    modify $ \s -> s { hsCs  = c : (hsCs s) }

addW   :: WfC -> CG ()  
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive definitions.

addKuts :: SpecType -> CG ()
addKuts !t = modify $ \s -> s { kuts = {- tracePpr "KUTS: " $-} updKuts (kuts s) t }
  where updKuts :: F.Kuts -> SpecType -> F.Kuts
        updKuts = foldReft (F.ksUnion . (F.reftKVars . ur_reft) )


-- | Used for annotation binders (i.e. at binder sites)

addIdA :: Var -> Annot -> CG ()
addIdA !x !t  = modify $ \s -> s { annotMap = addA (getSrcSpan x) (Just x) t $ annotMap s } 

-- | Used for annotating reads (i.e. at Var x sites) 

addLocA :: Maybe Var -> SrcSpan -> Annot -> CG ()
addLocA !xo !l !t 
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }

-- | Used to update annotations for a location, due to (ghost) predicate applications

updateLocA (_:_)  (Just l) t = addLocA Nothing l (Left t)
updateLocA _      _        _ = return () 

addA !l !xo@(Just _)  !t !(AI m) 
  | isGoodSrcSpan l -- && not (l `M.member` m)
  = AI $ M.insert l (xo, t) m
addA !l !xo@(Nothing) !t !(AI m) 
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

-- | Right now, we generate NO new pvars. Rather than clutter code 
-- with `uRType` calls, put it in one place where the above invariant
-- is /obviously/ enforced.

freshTy   :: CoreExpr -> Type -> CG SpecType 
freshTy _ = liftM uRType . refresh . ofType 


-- To revert to the old setup, just do
-- freshTy_pretty = freshTy
-- freshTy_pretty e τ = refresh $ {-traceShow ("exprRefType: " ++ showPpr e) $-} exprRefType e
freshTy_pretty e _ = do t <- refresh $ {-traceShow ("exprRefType: " ++ showPpr e) $-} exprRefType e
                        return $ uRType t


-- TODO: remove freshRSort?
-- freshRSort :: CoreExpr -> RSort -> CG SpecType
-- freshRSort e = freshTy e . toType 

trueTy  :: Type -> CG SpecType
trueTy t 
  = do t   <- true $ ofType t
       tyi <- liftM tyConInfo get
       return $ addTyConInfo tyi (uRType t)

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

instance Freshable (F.Refa) where
  fresh = liftM (`F.RKvar` F.emptySubst) freshK
    where freshK = liftM F.intKvar fresh

instance Freshable [F.Refa] where
  fresh = liftM single fresh

instance Freshable (F.Reft) where
  fresh                   = errorstar "fresh Reft"
  true    (F.Reft (v, _)) = return $ F.Reft (v, []) 
  refresh (F.Reft (v, _)) = liftM (F.Reft . (v, )) fresh

instance Freshable RReft where
  fresh             = errorstar "fresh RReft"
  true (U r _)      = liftM uTop (true r)  
  refresh (U r _)   = liftM uTop (refresh r) 

instance Freshable RefType where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

trueRefType (RAllT α t)       
  = liftM (RAllT α) (true t)
trueRefType (RAllP π t)       
  = liftM (RAllP π) (true t)
trueRefType (RFun _ t t' _)    
  = liftM3 rFun fresh (true t) (true t')
trueRefType (RApp c ts _ _)  
  = liftM (\ts -> RApp c ts truerefs top) (mapM true ts)
		where truerefs = (RPoly . ofRSort . ptype) <$> (rTyConPs c)
trueRefType t                
  = return t

refreshRefType (RAllT α t)       
  = liftM (RAllT α) (refresh t)
refreshRefType (RAllP π t)       
  = liftM (RAllP π) (refresh t)
refreshRefType (RFun b t t' _)
  | b == F.dummySymbol -- b == (RB F.dummySymbol)
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
refreshRef (RMono _) = error "refreshRef: unexpected"

-- isBaseTyCon c
--   | c == intTyCon 
--   = True
--   | c == boolTyCon
--   = True
--   | otherwise
--   = False

addTyConInfo = mapBot . expandRApp

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------

-------------------------------------------------------------------
consCB :: CGEnv -> CoreBind -> CG CGEnv 
-------------------------------------------------------------------

consCB γ (Rec xes) 
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       let xts = [(x, to) | (x, _, to) <- xets, not (isGrty x)]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind γ') xets
       return γ' 
    where isGrty x = (varSymbol x) `memberREnv` (grtys γ)

consCB γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing) 
       to' <- consBind γ (x, e, to)
       extender γ (x, to')

consBind γ (x, e, Just spect) 
  = do let γ' = (γ `setLoc` getSrcSpan x) `setBind` x 
       t <- consE γ' e
       addSpecC (SubC γ t spect)       
--     cconsE γ' e t
       addIdA x (Left spect)
       return Nothing 

consBind γ (x, e, Nothing) 
   = do t <- unifyVar γ x <$> consE (γ `setBind` x) e
        addIdA x (Left t)
        return $ Just t

extender γ (x, Just t) = γ ++= ("extender", varSymbol x, t)
extender γ _           = return γ

addBinders γ0 x' cbs   = foldM (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]


varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Maybe SpecType)
varTemplate γ (x, eo)
  = case (eo, lookupREnv (varSymbol x) (grtys γ)) of
      (_, Just t) -> return $ Just t
      (Just e, _) -> do t  <- unifyVar γ x <$> freshTy_pretty e (exprType e)
                        addW (WfC γ t)
                        addKuts t
                        return $ Just t
      (_,      _) -> return Nothing

unifyVar γ x rt = unify (getPrType γ (varSymbol x)) rt

-------------------------------------------------------------------
-------------------- Generation: Expression -----------------------
-------------------------------------------------------------------

----------------------- Type Checking -----------------------------
cconsE :: CGEnv -> Expr Var -> SpecType -> CG () 
-------------------------------------------------------------------

cconsE γ (Let b e) t    
  = do γ'  <- consCB γ b
       cconsE γ' e t 

cconsE γ (Case e x _ cases) t 
  = do γ'  <- consCB γ $ NonRec x e
       forM_ cases $ cconsCase γ' x t nonDefAlts 
    where nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]

cconsE γ (Lam α e) (RAllT α' t) | isTyVar α 
  = cconsE γ e $ subsTyVar_meet' (α', rVar α) t 

cconsE γ (Lam x e) (RFun y ty t _) 
  | not (isTyVar x) 
  = do γ' <- (γ, "cconsE") += (varSymbol x, ty)
       cconsE γ' e (t `F.subst1` (y, F.EVar $ varSymbol x))
       addIdA x (Left ty) 

cconsE γ (Tick tt e) t   
  = cconsE (γ `setLoc` tt') e t
    where tt' = {- traceShow ("tickSrcSpan: e = " ++ showPpr e) $ -} tickSrcSpan tt

cconsE γ (Cast e _) t     
  = cconsE γ e t 

cconsE γ e (RAllP (p@(PV _ _ _)) t)
  = do s <- truePredRef p
       cconsE γ e (replacePreds "cconsE" t [(p, RPoly s)])

cconsE γ e t
  = do te  <- consE γ e
       te' <- instantiatePreds γ e te
       addC (SubC γ te' t) ("cconsE" ++ showPpr e)

instantiatePreds γ e (RAllP p t)
  = do s <- freshPredRef γ e p
       return $ replacePreds "consE" t [(p, RPoly s)] 
instantiatePreds _ _ t
  = return t

----------------------- Type Synthesis ----------------------------
consE :: CGEnv -> Expr Var -> CG SpecType 
-------------------------------------------------------------------

consE γ (Var x)   
  = do addLocA (Just x) (loc γ) (varAnn γ x t)
       return t
    where t = varRefType γ x

consE γ (Lit c) 
  = return $ uRType $ literalRefType (emb γ) c

consE γ (App e (Type τ)) 
  = do RAllT α te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       t          <- if isGeneric α te then freshTy e τ {- =>> addKuts -} else trueTy τ
       addW       $ WfC γ t
       return     $ subsTyVar_meet' (α, t) te

consE γ e'@(App e a) | eqType (exprType a) predType 
  = do t0 <- consE γ e
       case t0 of
         RAllP p t -> do s  <- freshPredRef γ e' p
                         (return $ replacePreds "consE" t [(p, RPoly s)]) {- =>> addKuts -}
         _         -> return t0

consE γ e'@(App e a)               
  = do ([], πs, te)        <- bkUniv <$> consE γ e
       zs                  <- mapM (\π -> liftM ((π,) . RPoly) $ freshPredRef γ e' π) πs
       te'                 <- return (replacePreds "consE" te zs) {- =>> addKuts -}
       _                   <- updateLocA πs (exprLoc e) te' 
       let (RFun x tx t _) = checkFun ("Non-fun App with caller", e') te' 
       cconsE γ a tx 
       return $ maybe err (F.subst1 t . (x,)) (argExpr γ a)
    where err = errorstar $ "consE: App crashes on" ++ showPpr a 

 

consE γ (Lam α e) | isTyVar α 
  = liftM (RAllT (rTyVar α)) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy (Var x) τx 
       γ'     <- ((γ, "consE") += (varSymbol x, tx))
       t1     <- consE γ' e1
       addIdA x (Left tx) 
       addW   $ WfC γ tx 
       return $ rFun (varSymbol x) tx t1
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

consE _ e	    
  = errorstar $ "consE cannot handle " ++ showPpr e

cconsFreshE γ e
  = do t   <- freshTy e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> (AltCon, [Var], CoreExpr) -> CG ()
-------------------------------------------------------------------------------------

cconsCase γ x t _ (DataAlt c, ys, ce) 
 = do let cbs          = zip (x':ys') (xt:yts)
      cγ              <- addBinders γ x' cbs
      cconsE cγ ce t
 where (x':ys')        = varSymbol <$> (x:ys)
       xt0             = checkTyCon ("checkTycon cconsCase", x) $ γ ?= x'
       tdc             = γ ?= (dataConSymbol c)
       (rtd, yts, _  ) = unfoldR tdc xt0 ys'
       r1              = dataConReft   c   ys' 
       r2              = dataConMsReft rtd ys'
       xt              = xt0 `strengthen` (uTop (r1 `meet` r2))

cconsCase γ x t acs (a, _, ce) 
  = do let x'  = varSymbol x
       let xt' = (γ ?= x') `strengthen` uTop (altReft γ acs a) 
       cγ     <- addBinders γ x' [(x', xt')]
       cconsE cγ ce t

altReft γ _ (LitAlt l)   = literalReft (emb γ) l
altReft γ acs DEFAULT    = mconcat [notLiteralReft l | LitAlt l <- acs]
  where notLiteralReft   = F.notExprReft . snd . literalConst (emb γ)
altReft _ _ _            = error "Constraint : altReft"

-- mkyts γ ys yts 
--   = liftM (reverse . snd) $ foldM mkyt (γ, []) $ zip ys yts
-- mkyt (γ, ts) (y, yt)
--   = do t' <- freshTy (Var y) (toType yt)
--        addC (SubC γ yt t') "mkyts"
--        addW (WfC γ t') 
--        return (γ ++= ("mkyt", varSymbol y, t'), t':ts) 

unfoldR td (RApp _ ts rs _) ys = (t3, yts, rt)
  where (vs, ps, t0)    = bkUniv td
        t1              = foldl' (flip subsTyVar_meet') t0 (zip vs ts)
        t2              = replacePreds "unfoldR" t1 $ safeZip "unfoldR" (reverse ps) rs
        (ys0, yts', rt) =  bkArrow t2
        (t3:yts)        = F.subst su <$> (t2:yts')
        su              = F.mkSubst [(x, F.EVar y)| (x, y)<- zip ys0 ys]
unfoldR _  _                _  = error "Constraint.hs : unfoldR"

instance Show CoreExpr where
  show = showSDoc . ppr

checkTyCon _ t@(RApp _ _ _ _) = t
checkTyCon x t                = checkErr x t --errorstar $ showPpr x ++ "type: " ++ showPpr t

-- checkRPred _ t@(RAll _ _)     = t
-- checkRPred x t                = checkErr x t

checkFun _ t@(RFun _ _ _ _)   = t
checkFun x t                  = checkErr x t

checkAll _ t@(RAllT _ _)      = t
checkAll x t                  = checkErr x t

checkErr (msg, e) t          = errorstar $ msg ++ showPpr e ++ "type: " ++ showPpr t

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

truePredRef ::  PVar (RRType r) -> CG SpecType
truePredRef (PV _ τ _)
  = trueTy (toType τ)

freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG SpecType 
freshPredRef γ e (PV _ τ as)
  = do t  <- freshTy e (toType τ)
       γ' <- foldM (++=) γ (map (\(τ, x, _) -> ("freshPredRef", x, ofRSort τ)) as) 
       addW $ WfC γ' t
       return t

-- tySort (RVar _ (F.Reft(_, [a])))     = a
-- tySort (RApp _ _ _ (F.Reft(_, [a]))) = a
-- tySort _                             = error "tySort"

-----------------------------------------------------------------------
---------- Helpers: Creating Refinement Types For Various Things ------
-----------------------------------------------------------------------

argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr _ (Var vy)    = Just $ F.EVar $ varSymbol vy
argExpr γ (Lit c)     = Just $ snd $ literalConst (emb γ) c
argExpr γ (Tick _ e)  = argExpr γ e
argExpr _ e           = errorstar $ "argExpr: " ++ (showPpr e)

varRefType γ x =  t 
  where t  = (γ ?= (varSymbol x)) `strengthen` xr
        xr = uTop $ F.symbolReft $ varSymbol x

-- TODO: should only expose/use subt. Not subsTyVar_meet
subsTyVar_meet' (α, t) = subsTyVar_meet (α, toRSort t, t)

-----------------------------------------------------------------------
--------------- Forcing Strictness ------------------------------------
-----------------------------------------------------------------------

instance NFData Cinfo 

instance NFData CGEnv where
  rnf (CGE x1 x2 x3 x4 x5 x6 x7 x8 _ x9 x10) 
    = x1 `seq` rnf x2 `seq` seq x3 `seq` x4 `seq` rnf x5 `seq` 
      rnf x6  `seq` x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10

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

instance NFData CGInfo where
  rnf x = ({-# SCC "CGIrnf1" #-}  rnf (hsCs x))       `seq` 
          ({-# SCC "CGIrnf2" #-}  rnf (hsWfs x))      `seq` 
          ({-# SCC "CGIrnf3" #-}  rnf (fixCs x))      `seq` 
          ({-# SCC "CGIrnf4" #-}  rnf (fixWfs x))     `seq` 
          ({-# SCC "CGIrnf5" #-}  rnf (globals x))    `seq` 
          ({-# SCC "CGIrnf6" #-}  rnf (freshIndex x)) `seq`
          ({-# SCC "CGIrnf7" #-}  rnf (binds x))      `seq`
          ({-# SCC "CGIrnf8" #-}  rnf (annotMap x))   `seq`
          ({-# SCC "CGIrnf9" #-}  rnf (specQuals x))  `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kuts x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (lits x)) 

-------------------------------------------------------------------------------
--------------------- Reftypes from Fixpoint Expressions ----------------------
-------------------------------------------------------------------------------

existentialRefType     :: CGEnv -> SpecType -> SpecType
existentialRefType γ t = withReft t (uTop r') 
  where r'             = maybe top (exReft γ) (F.isSingletonReft r)
        r              = F.sr_reft $ rTypeSortedReft (emb γ) t


exReft γ (F.EApp f es) = F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
  where (xs,_ , t)     = bkArrow $ thd3 $ bkUniv $ exReftLookup γ f 
        su             = F.mkSubst $ safeZip "fExprRefType" xs es

exReft γ (F.EVar x)    = F.sr_reft $ rTypeSortedReft (emb γ) t 
  where (_,_ , t)      = bkArrow $ thd3 $ bkUniv $ exReftLookup γ x 

exReft _ e             = F.exprReft e 

exReftLookup γ x       = γ ?= x' 
  where x'             = fromMaybe err (varSymbol <$> F.lookupSEnv x γ')
        γ'             = syenv γ
        err            = errorstar $ "exReftLookup: unknown " ++ showPpr x ++ " in " ++ showPpr  γ'
withReft (RApp c ts rs _) r' = RApp c ts rs r' 
withReft (RVar a _) r'       = RVar a      r' 
withReft t _                 = t 

-------------------------------------------------------------------------------
-------------------- Cleaner Signatures For Rec-bindings ----------------------
-------------------------------------------------------------------------------

exprLoc                         :: CoreExpr -> Maybe SrcSpan

exprLoc (Tick tt _)             = Just $ tickSrcSpan tt
exprLoc (App e a) | isType a    = exprLoc e
exprLoc _                       = Nothing

isType (Type _)                 = True
isType a                        = eqType (exprType a) predType


exprRefType :: CoreExpr -> RefType 
exprRefType = exprRefType_ M.empty 

exprRefType_ :: M.HashMap Var RefType -> CoreExpr -> RefType 
exprRefType_ γ (Let b e) 
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e) 
  = rFun (varSymbol x) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x) 
  = M.lookupDefault (ofType $ varType x) x γ

exprRefType_ _ e
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

type RTyConInv = M.HashMap RTyCon F.Reft

addRTyConInv :: RTyConInv -> SpecType -> SpecType
addRTyConInv m t@(RApp c _ _ _) 
  = fromMaybe t ((strengthen t . uTop) <$> M.lookup c m)
addRTyConInv _ t 
  = t 

mkRTyConInv    :: [SpecType] -> RTyConInv 
mkRTyConInv ts = mconcat <$> group [ (c, r) | RApp c _ _ (U r _) <- strip <$> ts]
                 where strip = thd3 . bkUniv 


---------------------------------------------------------------
----- Refinement Type Environments ----------------------------
---------------------------------------------------------------

newtype REnv = REnv  (M.HashMap F.Symbol SpecType) -- deriving (Data, Typeable)

instance Outputable REnv where
  ppr (REnv m)         = vcat $ map pprxt $ M.toList m
    where pprxt (x, t) = ppr x <> dcolon <> ppr t  

instance NFData REnv where
  rnf (REnv _) = () -- rnf m

fromListREnv              = REnv . M.fromList
deleteREnv x (REnv env)   = REnv (M.delete x env)
insertREnv x y (REnv env) = REnv (M.insert x y env)
lookupREnv x (REnv env)   = M.lookup x env
-- emptyREnv                 = REnv M.empty
memberREnv x (REnv env)   = M.member x env
-- domREnv (REnv env)        = M.keys env



