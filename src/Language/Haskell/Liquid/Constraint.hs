{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}

-- | This module defines the representation of Subtyping and WF Constraints, and 
-- the code for syntax-directed constraint generation. 

module Language.Haskell.Liquid.Constraint (
    
    -- * Constraint information output by generator 
    CGInfo (..)
  
    -- * Function that does the actual generation
  , generateConstraints
    
    -- * Project Constraints to Fixpoint Format
  , cgInfoFInfo , cgInfoFInfoBot, cgInfoFInfoKvars
  
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
import Var
import Id
import Name            -- (getSrcSpan, getOccName)
import Text.PrettyPrint.HughesPJ

import Control.Monad.State

import Control.Applicative      ((<$>))
import Control.Exception.Base

import Data.Monoid              (mconcat)
import Data.Maybe               (fromJust, isJust, fromMaybe, catMaybes)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import Data.Bifunctor
import Data.List (foldl')

import Text.Printf

import qualified Language.Haskell.Liquid.CTags      as Tg
import qualified Language.Fixpoint.Types            as F
import Language.Fixpoint.Names (dropModuleNames)
import Language.Fixpoint.Sort (pruneUnsortedReft)

import Language.Haskell.Liquid.Fresh

import Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.Annotate
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.PredType         hiding (freeTyVars)          
import Language.Haskell.Liquid.Predicates
import Language.Haskell.Liquid.PrettyPrint
import Language.Haskell.Liquid.GhcMisc          (isInternal, collectArguments, getSourcePos, pprDoc, tickSrcSpan, hasBaseTypeVar, showPpr)
import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Qualifier
import Control.DeepSeq

import Debug.Trace (trace)
import IdInfo
-----------------------------------------------------------------------
------------- Constraint Generation: Toplevel -------------------------
-----------------------------------------------------------------------

generateConstraints      :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI cfg info
  where 
    act                  = consAct (info {cbs = fst pds}) (snd pds)
    pds                  = generatePredicates info
    cfg                  = config $ spec info

consAct info penv
  = do γ     <- initEnv info penv
       foldM consCBTop γ (cbs info)
       hcs <- hsCs  <$> get 
       hws <- hsWfs <$> get
       fcs <- concat <$> mapM splitC hcs 
       fws <- concat <$> mapM splitW hws
       modify $ \st -> st { fixCs = fcs } { fixWfs = fws }

initEnv :: GhcInfo -> F.SEnv PrType -> CG CGEnv  
initEnv info penv
  = do let tce   = tcEmbeds $ spec info
       defaults <- forM (impVars info) $ \x -> liftM (x,) (trueTy $ varType x)
       tyi      <- tyConInfo <$> get 
       let f0    = grty info                        -- asserted refinements     (for defined vars)
       f0''     <- grtyTop info                     -- default TOP reftype      (for exported vars without spec) 
       let f0'   = if (notruetypes $ config $ spec info) then [] else f0'' 
       let f1    = defaults                         -- default TOP reftype      (for all vars) 
       f2       <- refreshArgs' $ assm info         -- assumed refinements      (for imported vars)
       f3       <- refreshArgs' $ ctor' $ spec info -- constructor refinements  (for measures)
       let bs    = (map (unifyts' tce tyi penv)) <$> [f0 ++ f0', f1, f2, f3]
       lts      <- lits <$> get
       let tcb   = mapSnd (rTypeSort tce ) <$> concat bs
       let γ0    = measEnv (spec info) penv (head bs) (cbs info) (tcb ++ lts)
       foldM (++=) γ0 [("initEnv", x, y) | (x, y) <- concat bs]
  where refreshArgs' = mapM (mapSndM refreshArgs)
  -- where tce = tcEmbeds $ spec info 

ctor' = map (mapSnd val) . ctors

unifyts' tce tyi penv = (second (addTyConInfo tce tyi)) . (unifyts penv)

unifyts penv (x, t) = (x', unify pt t)
 where pt = F.lookupSEnv x' penv
       x' = F.symbol x

measEnv sp penv xts cbs lts
  = CGE { loc   = noSrcSpan
        , renv  = fromListREnv $ second (uRType . val) <$> meas sp
        , syenv = F.fromListSEnv $ freeSyms sp
        , penv  = penv 
        , fenv  = initFEnv $ lts ++ (second (rTypeSort tce . val) <$> meas sp)
        , recs  = S.empty 
        , invs  = mkRTyConInv    $ invariants sp
        , grtys = fromListREnv xts 
        , emb   = tce 
        , tgEnv = Tg.makeTagEnv cbs
        , tgKey = Nothing
        , trec  = Nothing
        , lcb   = M.empty
        } 
    where
      tce = tcEmbeds sp

assm = assm_grty impVars 
grty = assm_grty defVars

assm_grty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ] 
  where 
    xs           = S.fromList $ f info 
    sigs         = tySigs     $ spec info  

grtyTop info     = forM topVs $ \v -> (v,) <$> (trueTy $ varType v) -- val $ varSpecType v) | v <- defVars info, isTop v]
  where
    topVs        = filter isTop $ defVars info
    isTop v      = isExportedId v && not (v `S.member` useVs) && not (v `S.member` sigVs)
    useVs        = S.fromList $ useVars info
    sigVs        = S.fromList $ [v | (v,_) <- tySigs $ spec info]


------------------------------------------------------------------------
-- | Helpers: Reading/Extending Environment Bindings -------------------
------------------------------------------------------------------------

data FEnv = FE { fe_binds :: !F.IBindEnv      -- ^ Integer Keys for Fixpoint Environment
               , fe_env   :: !(F.SEnv F.Sort) -- ^ Fixpoint Environment
               }

insertFEnv (FE benv env) ((x, t), i)
  = FE (F.insertsIBindEnv [i] benv) (F.insertSEnv x t env)

insertsFEnv = L.foldl' insertFEnv

initFEnv init = FE F.emptyIBindEnv $ F.fromListSEnv (wiredSortedSyms ++ init)

data CGEnv 
  = CGE { loc    :: !SrcSpan           -- ^ Location in original source file
        , renv   :: !REnv              -- ^ SpecTypes for Bindings in scope
        , syenv  :: !(F.SEnv Var)      -- ^ Map from free Symbols (e.g. datacons) to Var
        , penv   :: !(F.SEnv PrType)   -- ^ PrTypes for top-level bindings (merge with renv) 
        , fenv   :: !FEnv              -- ^ Fixpoint Environment
        , recs   :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
        , invs   :: !RTyConInv         -- ^ Datatype invariants 
        , grtys  :: !REnv              -- ^ Top-level variables with (assert)-guarantees to verify
        , emb    :: F.TCEmb TC.TyCon   -- ^ How to embed GHC Tycons into fixpoint sorts
        , tgEnv :: !Tg.TagEnv          -- ^ Map from top-level binders to fixpoint tag
        , tgKey :: !(Maybe Tg.TagKey)  -- ^ Current top-level binder
        , trec  :: !(Maybe (M.HashMap F.Symbol SpecType)) -- ^ Type of recursive function with decreasing constraints
        , lcb   :: !(M.HashMap F.Symbol CoreExpr) -- ^ Let binding that have not been checked
        } -- deriving (Data, Typeable)

instance PPrint CGEnv where
  pprint = pprint . renv

instance Show CGEnv where
  show = showpp

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

withTRec γ xts = γ' {trec = Just $ M.fromList xts' `M.union` trec'}
  where γ'    = γ `withRecs` (fst <$> xts)
        trec' = fromMaybe M.empty $ trec γ
        xts'  = mapFst F.symbol <$> xts

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

-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t

-- isBase :: RType a -> Bool
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RFun _ t1 t2 _) = isBase t1 && isBase t2
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase _                = False

-----------------------------------------------------------------
------------------- Constraints: Types --------------------------
-----------------------------------------------------------------

data SubC     = SubC { senv  :: !CGEnv
                     , lhs   :: !SpecType
                     , rhs   :: !SpecType 
                     }
              | SubR { senv  :: !CGEnv
                     , ref   :: !RReft
                     }

data WfC      = WfC  !CGEnv !SpecType 
              -- deriving (Data, Typeable)

type FixSubC  = F.SubC Cinfo
type FixWfC   = F.WfC Cinfo

instance PPrint SubC where
  pprint c = pprint (senv c)
           $+$ ((text " |- ") <+> ( (pprint (lhs c)) 
                             $+$ text "<:" 
                             $+$ (pprint (rhs c))))

instance PPrint WfC where
  pprint (WfC w r) = pprint w <> text " |- " <> pprint r 


------------------------------------------------------------
------------------- Constraint Splitting -------------------
------------------------------------------------------------

splitW ::  WfC -> CG [FixWfC]

splitW (WfC γ t@(RFun x t1 t2 _)) 
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1) 
        γ'   <- (γ, "splitW") += (x, t1)
        ws'' <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t@(RAppTy t1 t2 _)) 
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1) 
        ws'' <- splitW (WfC γ t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (RAllT _ r)) 
  = splitW (WfC γ r)

splitW (WfC γ (RAllP _ r)) 
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ _))
  = bsplitW γ t 

splitW (WfC _ (RCls _ _))
  = return []

splitW (WfC γ t@(RApp _ ts rs _))
  =  do ws    <- bsplitW γ t 
        γ'    <- γ `extendEnvWithVV` t 
        ws'   <- concat <$> mapM splitW (map (WfC γ') ts)
        ws''  <- concat <$> mapM (rsplitW γ) rs
        return $ ws ++ ws' ++ ws''

splitW (WfC _ t) 
  = errorstar $ "splitW cannot handle: " ++ showpp t

rsplitW _ (RMono _ _)  
  = errorstar "Constrains: rsplitW for RMono"
rsplitW γ (RPoly ss t0) 
  = do γ' <- foldM (++=) γ [("rsplitC", x, ofRSort s) | (x, s) <- ss]
       splitW $ WfC γ' t0

bsplitW :: CGEnv -> SpecType -> CG [FixWfC]
bsplitW γ t = pruneRefs <$> get >>= return . bsplitW' γ t

bsplitW' γ t pflag
  | F.isNonTrivialSortedReft r' = [F.wfC (fe_binds $ fenv γ) r' Nothing ci] 
  | otherwise                   = []
  where 
    r'                          = rTypeSortedReft' pflag γ t
    ci                          = Ci (loc γ) Nothing

mkSortedReft tce = F.RR . rTypeSort tce

------------------------------------------------------------
splitC :: SubC -> CG [FixSubC]
------------------------------------------------------------

splitC (SubC γ (REx x tx t1) (REx x2 _ t2)) | x == x2
  = do γ' <- (γ, "addExBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (REx x tx t2)) 
  = do γ' <- (γ, "addExBind 1") += (x, forallExprRefType γ tx)
       let xs  = grapBindsWithType tx γ
       let t2' = splitExistsCases x xs tx t2
       splitC (SubC γ' t1 t2')

-- existential at the left hand side is treated like forall
splitC z@(SubC γ (REx x tx t1) t2) 
  = do -- let tx' = traceShow ("splitC: " ++ showpp z) tx 
       γ' <- (γ, "addExBind 1") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RAllE x tx t1) (RAllE x2 _ t2)) | x == x2
  = do γ' <- (γ, "addExBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)


splitC (SubC γ (RAllE x tx t1) t2)
  = do γ' <- (γ, "addExBind 2") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (RAllE x tx t2))
  = do γ' <- (γ, "addExBind 2") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RRTy r t1) t2) 
  = do c1 <- splitC (SubR γ r)
       c2 <- splitC (SubC γ t1 t2)
       return $ c1 ++ c2

splitC (SubC γ t1@(RFun x1 r1 r1' _) t2@(RFun x2 r2 r2' _)) 
  =  do cs       <- bsplitC γ t1 t2 
        cs'      <- splitC  (SubC γ r2 r1) 
        γ'       <- (γ, "splitC") += (x2, r2) 
        let r1x2' = r1' `F.subst1` (x1, F.EVar x2) 
        cs''     <- splitC  (SubC γ' r1x2' r2') 
        return    $ cs ++ cs' ++ cs''

splitC (SubC γ t1@(RAppTy r1 r1' _) t2@(RAppTy r2 r2' _)) 
  =  do cs    <- bsplitC γ t1 t2 
        cs'   <- splitC  (SubC γ r1 r2) 
        cs''  <- splitC  (SubC γ r1' r2') 
        return $ cs ++ cs' ++ cs''

splitC (SubC γ t1 (RAllP p t))
  = splitC $ SubC γ t1 t'
  where t' = fmap (replacePredsWithRefs su) t
        su = (uPVar p, pVartoRConc p)

splitC (SubC _ t1@(RAllP _ _) t2) 
  = errorstar $ "Predicate in lhs of constrain:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2
--   = splitC $ SubC γ t' t2
--   where t' = fmap (replacePredsWithRefs su) t
--        su = (uPVar p, pVartoRConc p)

splitC (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2 
  = splitC $ SubC γ t1 t2
  | otherwise   
  = splitC $ SubC γ t1 t2' 
  where t2' = subsTyVar_meet' (α2, RVar α1 F.top) t2

splitC (SubC γ t1@(RApp _ _ _ _) t2@(RApp _ _ _ _))
  = do (t1',t2') <- unifyVV t1 t2
       cs    <- bsplitC γ t1' t2'
       γ'    <- γ `extendEnvWithVV` t1' 
       let RApp c  t1s r1s _ = t1'
       let RApp c' t2s r2s _ = t2'
       let tyInfo = rTyConInfo c
       cscov  <- splitCIndexed  γ' t1s t2s $ covariantTyArgs     tyInfo
       cscon  <- splitCIndexed  γ' t2s t1s $ contravariantTyArgs tyInfo
       cscov' <- rsplitCIndexed γ' r1s r2s $ covariantPsArgs     tyInfo
       cscon' <- rsplitCIndexed γ' r2s r1s $ contravariantPsArgs tyInfo
       return $ cs ++ cscov ++ cscon ++ cscov' ++ cscon'

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _)) 
  | a1 == a2
  = bsplitC γ t1 t2

splitC (SubC _ (RCls c1 _) (RCls c2 _)) | c1 == c2
  = return []

splitC c@(SubC _ t1 t2) 
  = errorstar $ "(Another Broken Test!!!) splitc unexpected: " ++ showpp t1 ++ "\n\n" ++ showpp t2

splitC (SubR γ r)
  = return [F.subC γ' F.PTrue r1 r2 Nothing tag ci]
  where
    γ'  = fe_binds $ fenv γ
    r1  = F.RR s $ F.toReft r
    r2  = F.RR s $ F.Reft (vv, [F.RConc $ F.PBexp $ F.EVar vv])
    vv  = F.S "vvRec"
    s   = F.FApp F.boolFTyCon []
    ci  = Ci src err
    err = Just $ ErrAssType src (text "termination type error") r
    tag = getTag γ
    src = loc γ 

splitCIndexed γ t1s t2s indexes 
  = concatMapM splitC (zipWith (SubC γ) t1s' t2s')
  where t1s' = (L.!!) t1s <$> indexes
        t2s' = (L.!!) t2s <$> indexes

rsplitCIndexed γ t1s t2s indexes 
  = concatMapM (rsplitC γ) (safeZip "rsplitC" t1s' t2s')
  where t1s' = (L.!!) t1s <$> indexes
        t2s' = (L.!!) t2s <$> indexes


bsplitC γ t1 t2 = pruneRefs <$> get >>= return . bsplitC' γ t1 t2

bsplitC' γ t1 t2 pflag
  | F.isFunctionSortedReft r1' && F.isNonTrivialSortedReft r2'
  = [F.subC γ' F.PTrue (r1' {F.sr_reft = F.top}) r2' Nothing tag ci]
  | F.isNonTrivialSortedReft r2'
  = [F.subC γ' F.PTrue r1'  r2' Nothing tag ci]
  | otherwise
  = []
  where 
    γ'  = fe_binds $ fenv γ
    r1' = rTypeSortedReft' pflag γ t1
    r2' = rTypeSortedReft' pflag γ t2
    ci  = Ci src err
    tag = getTag γ
    err = Just $ ErrSubType src (text "subtype") t1 t2 
    src = loc γ 

     

unifyVV t1@(RApp c1 _ _ _) t2@(RApp c2 _ _ _)
  = do vv     <- (F.vv . Just) <$> fresh
       return  $ (shiftVV t1 vv,  (shiftVV t2 vv) ) -- {rt_pargs = r2s'})

rsplitC _ (RMono _ _, RMono _ _) 
  = errorstar "RefTypes.rsplitC on RMono"

rsplitC γ (t1@(RPoly s1 r1), t2@(RPoly s2 r2))
  = do γ'  <-  foldM (++=) γ [("rsplitC1", x, ofRSort s) | (x, s) <- s2]
       splitC (SubC γ' (F.subst su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | (x, y) <- zip (fst <$> s1) (fst <$> s2)]

rsplitC _ _  
  = errorstar "rsplit Rpoly - RMono"


-----------------------------------------------------------
-------------------- Generation: Types --------------------
-----------------------------------------------------------

data CGInfo = CGInfo { hsCs       :: ![SubC]                      -- ^ subtyping constraints over RType
                     , hsWfs      :: ![WfC]                       -- ^ wellformedness constraints over RType
                     , fixCs      :: ![FixSubC]                   -- ^ subtyping over Sort (post-splitting)
                     , fixWfs     :: ![FixWfC]                    -- ^ wellformedness constraints over Sort (post-splitting)
                     , globals    :: !F.FEnv                      -- ^ ? global measures
                     , freshIndex :: !Integer                     -- ^ counter for generating fresh KVars
                     , binds      :: !F.BindEnv                   -- ^ set of environment binders
                     , annotMap   :: !(AnnInfo Annot)             -- ^ source-position annotation map
                     , tyConInfo  :: !(M.HashMap TC.TyCon RTyCon) -- ^ information about type-constructors
                     , specQuals  :: ![F.Qualifier]               -- ^ ? qualifiers in source files
                     , specDecr   :: ![(Var, [Int])]              -- ^ ? FIX THIS
                     , termExprs  :: !(M.HashMap Var [F.Expr])    -- ^ Terminating Metrics for Recursive functions
                     , specLVars  :: !(S.HashSet Var)             -- ^ Set of variables to ignore for termination checking
                     , specLazy   :: !(S.HashSet Var)             -- ^ ? FIX THIS
                     , tyConEmbed :: !(F.TCEmb TC.TyCon)          -- ^ primitive Sorts into which TyCons should be embedded
                     , kuts       :: !(F.Kuts)                    -- ^ Fixpoint Kut variables (denoting "back-edges"/recursive KVars)
                     , lits       :: ![(F.Symbol, F.Sort)]        -- ^ ? FIX THIS 
                     , tcheck     :: !Bool                        -- ^ ? FIX THIS
                     , pruneRefs  :: !Bool                        -- ^ prune unsorted refinements
                     , logWarn    :: ![String]                    -- ^ ? FIX THIS
                     , kvProf     :: !KVProf                      -- ^ Profiling distribution of KVars 
                     , recCount       :: !Int
                     } -- deriving (Data, Typeable)

instance PPrint CGInfo where 
  pprint cgi =  {-# SCC "ppr_CGI" #-} ppr_CGInfo cgi

ppr_CGInfo cgi 
  =  (text "*********** Constraint Information ***********")
  {- $$ (text "*********** Haskell SubConstraints ***********")
     $$ (pprintLongList $ hsCs  cgi)
     $$ (text "*********** Haskell WFConstraints ************")
     $$ (pprintLongList $ hsWfs cgi)
     $$ (text "*********** Fixpoint SubConstraints **********")
     $$ (F.toFix  $ fixCs cgi)
     $$ (text "*********** Fixpoint WFConstraints ************")
     $$ (F.toFix  $ fixWfs cgi)
     $$ (text "*********** Fixpoint Kut Variables ************")
     $$ (F.toFix  $ kuts cgi)
     $$ (text "*********** Literals in Source     ************")
     $$ (pprint $ lits cgi)
  -}
  $$ (text "*********** KVar Distribution *****************")
  $$ (pprint $ kvProf cgi)
  $$ (text "Recursive binders:" <+> pprint (recCount cgi))

type CG = State CGInfo

initCGI cfg info = CGInfo {
    hsCs       = [] 
  , hsWfs      = [] 
  , fixCs      = []
  , fixWfs     = [] 
  , globals    = globs
  , freshIndex = 0
  , binds      = F.emptyBindEnv
  , annotMap   = AI M.empty
  , tyConInfo  = tyi
  , specQuals  =  qualifiers spc
               ++ specificationQualifiers (maxParams cfg) (info {spec = spec'})
  , tyConEmbed = tce  
  , kuts       = F.ksEmpty 
  , lits       = coreBindLits tce info 
  , termExprs  = M.fromList $ texprs spc
  , specDecr   = decr spc
  , specLVars  = lvars spc
  , specLazy   = lazy spc
  , tcheck     = not $ notermination cfg
  , pruneRefs  = not $ noPrune cfg
  , logWarn    = []
  , kvProf     = emptyKVProf
  , recCount       = 0
  } 
  where 
    tce        = tcEmbeds spc 
    spc        = spec info
    spec'      = spc {tySigs = [ (x, addTyConInfo tce tyi <$> t) | (x, t) <- tySigs spc] }
    tyi        = makeTyConInfo (tconsP spc)
    globs      = F.fromListSEnv . map mkSort $ meas spc
    mkSort     = mapSnd (rTypeSortedReft tce . val)
                               

coreBindLits tce info
  = sortNub      $ [ (x, so) | (_, Just (F.ELit x so)) <- lconsts]
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons]
  where 
    lconsts      = literalConst tce <$> literals (cbs info)
    dcons        = filter isDCon $ impVars info
    dconToSort   = typeSort tce . expandTypeSynonyms . varType 
    dconToSym    = dataConSymbol . idDataCon
    isDCon x     = isDataConWorkId x && not (hasBaseTypeVar x)

extendEnvWithVV γ t 
  | F.isNontrivialVV vv
  = (γ, "extVV") += (vv, t)
  | otherwise
  = return γ
  where vv = rTypeValueVar t

{- see tests/pos/polyfun for why you need everything in fixenv -} 
(++=) :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
γ ++= (_, x, t') 
  = do idx   <- fresh
       let t  = normalize γ {-x-} idx t'  
       let γ' = γ { renv = insertREnv x t (renv γ) }  
       pflag <- pruneRefs <$> get
       is    <- if isBase t 
                  then liftM single $ addBind x $ rTypeSortedReft' pflag γ' t 
                  else addClassBind t 
       return $ γ' { fenv = insertsFEnv (fenv γ) is }

rTypeSortedReft' pflag γ 
  | pflag
  = pruneUnsortedReft (fe_env $ fenv γ) . f
  | otherwise
  = f 
  where f = rTypeSortedReft (emb γ)

(+++=) :: (CGEnv, String) -> (F.Symbol, CoreExpr, SpecType) -> CG CGEnv

(γ, msg) +++= (x, e, t) = (γ{lcb = M.insert x e (lcb γ)}, "+++=") += (x, t)

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
                              ++ "\n New: " ++ showpp r
                              ++ "\n Old: " ++ showpp (x `lookupREnv` (renv γ))
                        
γ -= x =  γ {renv = deleteREnv x (renv γ), lcb  = M.delete x (lcb γ)}

(??=) :: CGEnv -> F.Symbol -> CG SpecType
γ ??= x 
  = case M.lookup x (lcb γ) of
    Just e  -> consE (γ-=x) e
    Nothing -> return $ γ ?= x 

(?=) ::  CGEnv -> F.Symbol -> SpecType 
γ ?= x = fromMaybe err $ lookupREnv x (renv γ)
         where err = errorstar $ "EnvLookup: unknown " 
                               ++ showpp x 
                               ++ " in renv " 
                               ++ showpp (renv γ)

normalize' γ x idx t = traceShow ("normalize " ++ showpp x ++ " idx = " ++ show idx ++ " t = " ++ showpp t) $ normalize γ idx t

normalize γ idx 
  = addRTyConInv (invs γ) 
  . normalizeVV idx 
  . normalizePds

normalizeVV idx t@(RApp _ _ _ _)
  | not (F.isNontrivialVV (rTypeValueVar t))
  = shiftVV t (F.vv $ Just idx)

normalizeVV _ t 
  = t 

shiftVV t@(RApp _ ts _ r) vv' 
  = t { rt_args = F.subst1 ts (rTypeValueVar t, F.EVar vv') } 
      { rt_reft = (`F.shiftVV` vv') <$> r }

shiftVV t _ 
  = t -- errorstar $ "shiftVV: cannot handle " ++ showpp t

addBind :: F.Symbol -> F.SortedReft -> CG ((F.Symbol, F.Sort), F.BindId)
addBind x r 
  = do st          <- get
       let (i, bs') = F.insertBindEnv x r (binds st)
       put          $ st { binds = bs' }
       return ((x, F.sr_sort r), i) -- traceShow ("addBind: " ++ showpp x) i

addClassBind :: SpecType -> CG [((F.Symbol, F.Sort), F.BindId)]
addClassBind = mapM (uncurry addBind) . classBinds

-- addClassBind (RCls c ts)
--   | isNumericClass c
--   = do let numReft = F.trueSortedReft F.FNum
--        let numVars = [rTyVarSymbol a | (RVar a _) <- ts]
--        is         <- forM numVars (`addBind` numReft)
--        return is
-- addClassBind _ 
--   = return [] 

addC :: SubC -> String -> CG ()  
addC !c@(SubC _ t1 t2) _msg 
  = -- trace ("addC " ++ _msg++ showpp t1 ++ "\n <: \n" ++ showpp t2 ) $
     modify $ \s -> s { hsCs  = c : (hsCs s) }
addC !c _msg 
  = modify $ \s -> s { hsCs  = c : (hsCs s) }

addPost γ (RRTy r t) 
  = addC (SubR γ r) "precondition" >> return t
addPost _ t  
  = return t

addW   :: WfC -> CG ()  
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

addWarning   :: String -> CG ()  
addWarning w = modify $ \s -> s { logWarn = w : (logWarn s) }

-- | Used for annotation binders (i.e. at binder sites)

addIdA            :: Var -> Annot -> CG ()
addIdA !x !t      = modify $ \s -> s { annotMap = upd $ annotMap s }
  where 
    loc           = getSrcSpan x
    upd m@(AI z)  = if boundRecVar loc m then m else addA loc (Just x) t m
    -- loc        = traceShow ("addIdA: " ++ show x ++ " :: " ++ showpp t ++ " at ") $ getSrcSpan x

boundRecVar l (AI m) = not $ null [t | (_, RDf t) <- M.lookupDefault [] l m]


-- | Used for annotating reads (i.e. at Var x sites) 

addLocA :: Maybe Var -> SrcSpan -> Annot -> CG ()
addLocA !xo !l !t 
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }

-- | Used to update annotations for a location, due to (ghost) predicate applications

updateLocA (_:_)  (Just l) t = addLocA Nothing l (Use t)
updateLocA _      _        _ = return () 

addA !l !xo@(Just _)  !t !(AI m) 
  | isGoodSrcSpan l 
  = AI $ inserts l (xo, t) m
addA !l !xo@(Nothing) !t !(AI m) 
  | l `M.member` m                  -- only spans known to be variables
  = AI $ inserts l (xo, t) m
addA _ _ _ !a 
  = a

-------------------------------------------------------------------
------------------------ Generation: Freshness --------------------
-------------------------------------------------------------------

-- | Right now, we generate NO new pvars. Rather than clutter code 
--   with `uRType` calls, put it in one place where the above 
--   invariant is /obviously/ enforced.
--   Constraint generation should ONLY use @freshTy_type@ and @freshTy_expr@

freshTy_type        :: KVKind -> CoreExpr -> Type -> CG SpecType 
freshTy_type k _ τ  = freshTy_reftype k $ ofType τ

freshTy_expr        :: KVKind -> CoreExpr -> Type -> CG SpecType 
freshTy_expr k e _  = freshTy_reftype k $ exprRefType e

freshTy_reftype     :: KVKind -> RefType -> CG SpecType 
freshTy_reftype k τ = do t <- fmap uRType $ refresh τ 
                         addKVars k t
                         return t

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.

addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do when (True)    $ modify $ \s -> s { kvProf = updKVProf k kvars (kvProf s) }
                     when (isKut k) $ modify $ \s -> s { kuts   = F.ksUnion kvars   (kuts s)   }
  where
     kvars      = sortNub $ specTypeKVars t

isKut          :: KVKind -> Bool
isKut RecBindE = True
isKut _        = False


specTypeKVars :: SpecType -> [F.Symbol]
specTypeKVars = foldReft ((++) . (F.reftKVars . ur_reft)) []

-- freshTy e τ = do t <- uRType <$> (refresh $ ofType τ)
--                  return $ traceShow ("freshTy: " ++ showPpr e) t
-- To revert to the old setup, just do
-- freshTy_expr = freshTy
-- freshTy_expr e τ = refresh $ {-traceShow ("exprRefType: " ++ F.showFix e) $-} exprRefType e
-- freshTy_expr e _ = do t <- refresh $ {- traceShow ("exprRefType: " ++ showPpr e) $ -} exprRefType e
--                         return $ uRType t


trueTy  :: Type -> CG SpecType
trueTy t 
  = do t     <- true $ ofType t
       tyi   <- liftM tyConInfo get
       tce   <- tyConEmbed <$> get
       return $ addTyConInfo tce tyi (uRType t)

refreshArgs t 
  = do xs' <- mapM (\_ -> fresh) xs
       let su = F.mkSubst $ zip xs (F.EVar <$> xs')
       return $ mkArrow αs πs (zip xs' (F.subst su <$> ts)) (F.subst su tbd)
  where (αs, πs, t0)  = bkUniv t
        (xs, ts, tbd) = bkArrow t0

instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

instance TCInfo CG where
  getTyConInfo  = tyConInfo  <$> get
  getTyConEmbed = tyConEmbed <$> get
  	
addTyConInfo tce tyi = mapBot (expandRApp tce tyi)

-------------------------------------------------------------------------------
----------------------- TERMINATION TYPE ---------------------------------------
-------------------------------------------------------------------------------

makeDecrIndex :: (Var, SpecType)-> CG [Int]
makeDecrIndex (x, t) 
  = do hint <- checkHint' . L.lookup x . specDecr <$> get
       case dindex of
        Nothing -> addWarning msg >> return []
        Just i  -> return $ fromMaybe [i] hint
  where ts            = snd3 $ bkArrow $ thd3 $ bkUniv t
        checkHint'    = checkHint x ts isDecreasing
        dindex        = L.findIndex isDecreasing ts
        msg = printf "%s: No decreasing parameter" $ showPpr (getSrcSpan x)

recType ((_, []), (_, [], t))
  = t

recType ((vs, indexc), (x, index, t))
  = makeRecType t v dxt index       
  where v    = (vs !!)  <$> indexc
        dxt  = (xts !!) <$> index
        loc  = showPpr (getSrcSpan x)
        xts' = bkArrow $ thd3 $ bkUniv t
        xts  = zip (fst3 xts') (snd3 xts')
        msg' = printf "%s: No decreasing argument on %s with %s" 
        msg  = printf "%s: No decreasing parameter" loc
                  loc (showPpr x) (showPpr vs)

checkIndex (x, vs, t, index)
  = do mapM_ (safeLogIndex msg' vs)  index
       mapM  (safeLogIndex msg  ts) index
  where loc   = showPpr (getSrcSpan x)
        ts  = snd3 $ bkArrow $ thd3 $ bkUniv t
        msg'  = printf "%s: No decreasing argument on %s with %s" 
        msg   = printf "%s: No decreasing parameter" loc
                  loc (showPpr x) (showPpr vs)

-- MOVE THE SAME LENS CHECKS BEFORE - TO DO IT ONCE FOR ALL FUNCTIOS
--  makeRecType t vs dxs is | not sameLens
--    = errorstar "Constraint.makeRecType: invalid arguments"
--    where sameLens  = (length vs) == (length is) && (length dxs) == (length is)
--  

makeRecType t vs' dxs' is
  = mkArrow αs πs xts' tbd
  where xts'          = replaceN (last is) (makeDecrType vdxs) xts
        vdxs          = zip vs dxs
        xts           = zip xs ts
        vs            = vs'
        dxs           = dxs'
        (αs, πs, t0)  = bkUniv t
        (xs, ts, tbd) = bkArrow t0

safeLogIndex err ls n
  | n >= length ls
  = addWarning err >> return Nothing
  | otherwise 
  = return $ Just $ ls !! n

checkHint _ _ _ Nothing 
  = Nothing

checkHint x ts f (Just ns) | L.sort ns /= ns
  = errorstar $ printf "%s: The hints should be increasing" loc
  where loc = showPpr $ getSrcSpan x

checkHint x ts f (Just ns) 
  = Just $ catMaybes (checkValidHint x ts f <$> ns)

checkValidHint x ts f n
  | n < 0 || n >= length ts = errorstar err
  | f (ts L.!! n)           = Just n
  | otherwise               = errorstar err
  where err = printf "%s: Invalid Hint %d for %s" loc (n+1) (showPpr x)
        loc = showPpr $ getSrcSpan x

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------
consCBLet, consCBTop :: CGEnv -> CoreBind -> CG CGEnv 
-------------------------------------------------------------------

consCBLet γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck && (tcond cb strict)
       modify $ \s -> s{tcheck = tflag}
       γ' <- consCB tflag γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

consCBTop γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck && (tcond cb strict)
       modify $ \s -> s{tcheck = tflag}
       γ' <- consCB tflag γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

tcond cb strict
  = not $ any (\x -> S.member x strict || isInternal x) (binds cb)
  where binds (NonRec x _) = [x]
        binds (Rec xes)    = fst $ unzip xes

-------------------------------------------------------------------
consCB :: Bool -> CGEnv -> CoreBind -> CG CGEnv 
-------------------------------------------------------------------

consCBSizedTys tflag γ (Rec xes)
  = do xets     <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       ts       <- mapM refreshArgs $ (fromJust . thd3 <$> xets)
       let vs    = zipWith collectArgs ts es
       is       <- checkSameLens <$> mapM makeDecrIndex (zip xs ts)
       let xeets = (\vis -> [(vis, x) | x <- zip3 xs is ts]) <$> (zip vs is)
       checkEqTypes . L.transpose <$> mapM checkIndex (zip4 xs vs ts is)
       let rts   = (recType <$>) <$> xeets
       let xts   = zip xs (Just <$> ts)
       γ'       <- foldM extender γ xts
       let γs    = [γ' `withTRec` (zip xs rts') | rts' <- rts]
       let xets' = zip3 xs es (Just <$> ts)
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where 
       dmapM f  = sequence . (mapM f <$>)
       (xs, es) = unzip xes
       collectArgs   = collectArguments . length . fst3 . bkArrow . thd3 . bkUniv
       checkEqTypes  = map (checkAll err1 toRSort . catMaybes)
       checkSameLens = checkAll err2 length
       err1          = printf "%s: The decreasing parameters should be of same type" loc
       err2          = printf "%s: All Recursive functions should have the same number of decreasing parameters" loc
       loc           = showPpr $ getSrcSpan (head xs)

       checkAll _   _ []            = []
       checkAll err f (x:xs) 
         | all (==(f x)) (f <$> xs) = (x:xs)
         | otherwise                = errorstar err

consCBWithExprs γ xtes (Rec xes) 
  = do xets     <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       let ts    = safeFromJust err . thd3 <$> xets
       ts'      <- mapM refreshArgs ts
       let xts   = zip xs (Just <$> ts')
       γ'       <- foldM extender γ xts
       let γs    = makeTermEnvs γ' xtes xes ts ts'
       let xets' = zip3 xs es (Just <$> ts')
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where (xs, es) = unzip xes
        err      = "Constant: consCBWithExprs"

makeTermEnvs γ xtes xes ts ts'
  = (\rt -> γ `withTRec` (zip xs rt)) <$> rts
  where vs   = zipWith collectArgs ts es
        ys   = (fst3 . bkArrowDeep) <$> ts 
        ys'  = (fst3 . bkArrowDeep) <$> ts'
        sus' = zipWith mkSub ys ys'
        sus  = zipWith mkSub ys ((F.symbol <$>) <$> vs)
        ess  = (\x -> (safeFromJust (err x) $ (x `L.lookup` xtes))) <$> xs
        tes  = zipWith (\su es -> F.subst su <$> es)  sus ess 
        tes' = zipWith (\su es -> F.subst su <$> es)  sus' ess 
        rss  = zipWith makeLexRefa tes' <$> (repeat <$> tes)
        rts  = zipWith addTermCond ts' <$> rss
        (xs, es)     = unzip xes
        mkSub ys ys' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip ys ys']
        collectArgs  = collectArguments . length . fst3 . bkArrow . thd3 . bkUniv
        err x = "Constant: makeTermEnvs: no terminating expression for " ++ showPpr x 
       
consCB tflag γ (Rec xes) | tflag 
  = do texprs <- termExprs <$> get
       modify $ \i -> i { recCount = recCount i + length xes }
       let xxes = catMaybes $ (`lookup` texprs) <$> xs
       if null xxes 
         then consCBSizedTys tflag γ (Rec xes)
         else check xxes <$> consCBWithExprs γ xxes (Rec xes)
  where xs = fst $ unzip xes
        check ys r | length ys == length xs = r
                   | otherwise              = errorstar err
        err = printf "%s: Termination expressions should be provided for ALL mutual recursive functions" loc
        loc = showPpr $ getSrcSpan (head xs)
        lookup k m | Just x <- M.lookup k m = Just (k, x)
                   | otherwise              = Nothing

-- TODO : no termination check:
-- check that the result type is trivial!
consCB _ γ (Rec xes) 
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets, not (isGrty x)]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ' 
    where isGrty x = (F.symbol x) `memberREnv` (grtys γ)

consCB _ γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing) 
       to' <- consBind False γ (x, e, to)
       extender γ (x, to')

consBind isRec γ (x, e, Just spect) 
  = do let γ' = (γ `setLoc` getSrcSpan x) `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e spect
       addIdA x (defAnn isRec spect)
       return Nothing
  where πs   = snd3 $ bkUniv spect

consBind isRec γ (x, e, Nothing)
  = do t <- unifyVar γ x <$> consE (γ `setBind` x) e
       addIdA x (defAnn isRec t)
       return $ Just t

defAnn True  = RDf
defAnn False = Def

addPToEnv γ π
  = do γπ <- γ ++= ("addSpec1", pname π, toPredType π)
       foldM (++=) γπ [("addSpec2", x, ofRSort t) | (t, x, _) <- pargs π]

extender γ (x, Just t) = γ ++= ("extender", F.symbol x, t)
extender γ _           = return γ

addBinders γ0 x' cbs   = foldM (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.

varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Maybe SpecType)
varTemplate γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ)) of
      (_, Just t) -> return $ Just t
      (Just e, _) -> do t  <- unifyVar γ x <$> freshTy_expr RecBindE e (exprType e)
                        addW (WfC γ t)
                        {- KVPROF addKuts t -}
                        return $ Just t
      (_,      _) -> return Nothing

unifyVar γ x rt = unify (getPrType γ (F.symbol x)) rt

-------------------------------------------------------------------
-------------------- Generation: Expression -----------------------
-------------------------------------------------------------------

----------------------- Type Checking -----------------------------
cconsE :: CGEnv -> Expr Var -> SpecType -> CG () 
-------------------------------------------------------------------
cconsE γ e@(Let b@(NonRec x _) ee) t
  = do sp <- specLVars <$> get
       if (x `S.member` sp) || isDefLazyVar x  
        then cconsLazyLet γ e t 
        else do γ'  <- consCBLet γ b
                cconsE γ' ee t
  where
       isDefLazyVar = L.isPrefixOf "fail" . showPpr

cconsE γ (Let b e) t    
  = do γ'  <- consCBLet γ b
       cconsE γ' e t 

cconsE γ (Case e x _ cases) t 
  = do γ'  <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase γ' x t nonDefAlts 
    where 
       nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]

cconsE γ (Lam α e) (RAllT α' t) | isTyVar α 
  = cconsE γ e $ subsTyVar_meet' (α', rVar α) t 

cconsE γ (Lam x e) (RFun y ty t _) 
  | not (isTyVar x) 
  = do γ' <- (γ, "cconsE") += (F.symbol x, ty)
       cconsE γ' e (t `F.subst1` (y, F.EVar $ F.symbol x))
       addIdA x (Def ty) 

cconsE γ (Tick tt e) t   
  = cconsE (γ `setLoc` tickSrcSpan tt) e t

cconsE γ e@(Cast e' _) t     
  = do t' <- castTy (exprType e) e' -- trueTy $ exprType e
       addC (SubC γ t' t) ("cconsE Cast" ++ showPpr e) 

cconsE γ e (RAllP p t)
  = cconsE γ e t'
  where t' = fmap (replacePredsWithRefs su) t
        su = (uPVar p, pVartoRConc p)

cconsE γ e t
  = do te  <- consE γ e
       te' <- instantiatePreds γ e te
       addC (SubC γ te' t) ("cconsE" ++ showPpr e)

instantiatePreds γ e (RAllP p t)
  = do s <- freshPredRef γ e p
       return $ replacePreds "consE" t [(p, s)] 
instantiatePreds _ _ t
  = return t

cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- {-(`strengthen` xr) <$>-} trueTy (varType x)
       γ' <- (γ, "Let NonRec") +++= (x', ex, tx)
       cconsE γ' e t
  where xr = singletonReft x -- uTop $ F.symbolReft x'
        x' = F.symbol x


----------------------- Type Synthesis ----------------------------
consE :: CGEnv -> Expr Var -> CG SpecType 
-------------------------------------------------------------------

consE γ (Var x)   
  = do t <- varRefType γ x
       addLocA (Just x) (loc γ) (varAnn γ x t)
       return t

consE γ (Lit c) 
  = return $ uRType $ literalFRefType (emb γ) c

consE γ (App e (Type τ)) 
  = do RAllT α te <- liftM (checkAll ("Non-all TyApp with expr", e)) $ consE γ e
       t          <- if isGeneric α te then freshTy_type TypeInstE e τ {- =>> addKuts -} else trueTy τ
       addW       $ WfC γ t
       return     $ subsTyVar_meet' (α, t) te

consE γ e'@(App e a) | eqType (exprType a) predType 
  = do t0 <- consE γ e
       case t0 of
         RAllP p t -> do s <- freshPredRef γ e' p
                         return $ replacePreds "consE" t [(p, s)] {- =>> addKuts -}
         _         -> return t0

consE γ e'@(App e a)               
  = do ([], πs, te)        <- bkUniv <$> consE γ e
       zs                  <- mapM (\π -> liftM ((π,)) $ freshPredRef γ e' π) πs
       te'                 <- return (replacePreds "consE" te zs) {- =>> addKuts -}
       (γ', te'')          <- dropExists γ te'
       updateLocA πs (exprLoc e) te'' 
       let (RFun x tx t _) = checkFun ("Non-fun App with caller ", e') te''
       cconsE γ' a tx 
       addPost γ' $ maybe (checkUnbound γ' e' x t) (F.subst1 t . (x,)) (argExpr γ a)
--    where err = errorstar $ "consE: App crashes on" ++ showPpr a 


consE γ (Lam α e) | isTyVar α 
  = liftM (RAllT (rTyVar α)) (consE γ e) 

consE γ  e@(Lam x e1) 
  = do tx     <- freshTy_type LamE (Var x) τx 
       γ'     <- ((γ, "consE") += (F.symbol x, tx))
       t1     <- consE γ' e1
       addIdA x (Def tx) 
       addW   $ WfC γ tx 
       return $ rFun (F.symbol x) tx t1
    where FunTy τx _ = exprType e 

-- EXISTS-BASED CONSTRAINTS HEREHEREHEREHERE
-- Currently suppressed because they break all sorts of invariants,
-- e.g. for `unfoldR`...
-- consE γ e@(Let b@(NonRec x _) e')
--   = do γ'    <- consCBLet γ b
--        consElimE γ' [F.symbol x] e'
-- 
-- consE γ (Case e x _ [(ac, ys, ce)]) 
--   = do γ'  <- consCBLet γ (NonRec x e)
--        γ'' <- caseEnv γ' x [] ac ys
--        consElimE γ'' (F.symbol <$> (x:ys)) ce 

consE γ e@(Let _ _) 
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ _) 
  = cconsFreshE CaseE γ e

consE γ (Tick tt e)
  = do t <- consE (γ `setLoc` l) e
       addLocA Nothing l (Use t)
       return t
    where l = {- traceShow ("tickSrcSpan: e = " ++ showPpr e) $ -} tickSrcSpan tt

consE γ e@(Cast e' _)      
  = castTy (exprType e) e'

consE γ e@(Coercion _)
   = trueTy $ exprType e

consE _ e	    
  = errorstar $ "consE cannot handle " ++ showPpr e 

castTy τ (Var x)
  = do t <- trueTy τ 
       return $  t `strengthen` (uTop $ F.uexprReft $ F.expr x)

castTy τ _
  = trueTy τ 

singletonReft = uTop . F.symbolReft . F.symbol 

-- | @consElimE@ is used to *synthesize* types by **existential elimination** 
--   instead of *checking* via a fresh template. That is, assuming
--      γ |- e1 ~> t1
--   we have
--      γ |- let x = e1 in e2 ~> Ex x t1 t2 
--   where
--      γ, x:t1 |- e2 ~> t2
--   instead of the earlier case where we generate a fresh template `t` and check
--      γ, x:t1 |- e <~ t

consElimE γ xs e
  = do t     <- consE γ e
       xts   <- forM xs $ \x -> (x,) <$> (γ ??= x)
       return $ rEx xts t

-- | @consFreshE@ is used to *synthesize* types with a **fresh template** when
-- the above existential elimination is not easy (e.g. at joins, recursive binders)

cconsFreshE kvkind γ e
  = do t   <- freshTy_type kvkind e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

checkUnbound γ e x t 
  | x `notElem` (F.syms t) = t
  | otherwise              = errorstar $ "consE: cannot handle App " ++ showPpr e ++ " at " ++ showPpr (loc γ)

dropExists γ (REx x tx t) = liftM (, t) $ (γ, "dropExists") += (x, tx)
dropExists γ t            = return (γ, t)

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> (AltCon, [Var], CoreExpr) -> CG ()
-------------------------------------------------------------------------------------
cconsCase γ x t acs (ac, ys, ce)
  = do cγ <- caseEnv γ x acs ac ys 
       cconsE cγ ce t

-------------------------------------------------------------------------------------
caseEnv   :: CGEnv -> Var -> [AltCon] -> AltCon -> [Var] -> CG CGEnv 
-------------------------------------------------------------------------------------
caseEnv γ x _   (DataAlt c) ys
  = do let (x' : ys')    = F.symbol <$> (x:ys)
       xt0              <- checkTyCon ("checkTycon cconsCase", x) <$> γ ??= x'
       tdc              <- γ ??= (dataConSymbol c)
       let (rtd, yts, _) = unfoldR c tdc (shiftVV xt0 x') ys
       let r1            = dataConReft   c   ys' 
       let r2            = dataConMsReft rtd ys'
       let xt            = xt0 `strengthen` (uTop (r1 `F.meet` r2))
       let cbs           = safeZip "cconsCase" (x':ys') (xt0:yts)
       cγ'              <- addBinders γ x' cbs
       cγ               <- addBinders cγ' x' [(x', xt)]
       return cγ 

caseEnv γ x acs a _ 
  = do let x'  = F.symbol x
       xt'    <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x')
       cγ     <- addBinders γ x' [(x', xt')]
       return cγ

-- cconsCase γ x t _ (DataAlt c, ys, ce) 
--  = do xt0              <- checkTyCon ("checkTycon cconsCase", x) <$> γ ??= x'
--       tdc              <- γ ??= (dataConSymbol c)
--       let (rtd, yts, _) = unfoldR c tdc (shiftVV xt0 x') ys
--       let r1            = dataConReft   c   ys' 
--       let r2            = dataConMsReft rtd ys'
--       let xt            = xt0 `strengthen` (uTop (r1 `F.meet` r2))
--       let cbs           = safeZip "cconsCase" (x':ys') (xt0:yts)
--       cγ'              <- addBinders γ x' cbs
--       cγ               <- addBinders cγ' x' [(x', xt)]
--       cconsE cγ ce t
--    where 
--       (x':ys')        = F.symbol <$> (x:ys)
-- 
-- 
-- cconsCase γ x t acs (a, _, ce) 
--        cconsE cγ ce t

altReft γ _ (LitAlt l)   = literalFReft (emb γ) l
altReft γ acs DEFAULT    = mconcat [notLiteralReft l | LitAlt l <- acs]
  where notLiteralReft   = maybe F.top F.notExprReft . snd . literalConst (emb γ)
altReft _ _ _            = error "Constraint : altReft"

unfoldR dc td (RApp _ ts rs _) ys = (t3, tvys ++ yts, rt)
  where 
        tbody           = instantiatePvs (instantiateTys td ts) $ reverse rs
        (ys0, yts', rt) = safeBkArrow $ instantiateTys tbody tvs'
        (t3:yts)        = F.subst su <$> (rt:yts')
        su              = F.mkSubst [(x, F.EVar y) | (x, y)<- zip ys0 ys']
        (αs, ys')       = mapSnd (F.symbol <$>) $ L.partition isTyVar ys
        tvs'            = rVar <$> αs
        tvys            = ofType . varType <$> αs

unfoldR _ _  _                _  = error "Constraint.hs : unfoldR"

instantiateTys = foldl' go
  where go (RAllT α tbody) t = subsTyVar_meet' (α, t) tbody
        go _ _               = errorstar "Constraint.instanctiateTy" 

instantiatePvs = foldl' go 
  where go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
        go _ _               = errorstar "Constraint.instanctiatePv" 

instance Show CoreExpr where
  show = showPpr

checkTyCon _ t@(RApp _ _ _ _) = t
checkTyCon x t                = checkErr x t --errorstar $ showPpr x ++ "type: " ++ showPpr t

-- checkRPred _ t@(RAll _ _)     = t
-- checkRPred x t                = checkErr x t

checkFun _ t@(RFun _ _ _ _)   = t
checkFun x t                  = checkErr x t

checkAll _ t@(RAllT _ _)      = t
checkAll x t                  = checkErr x t

checkErr (msg, e) t          = errorstar $ msg ++ showPpr e ++ ", type: " ++ showpp t

varAnn γ x t 
  | x `S.member` recs γ
  = Loc (getSrcSpan' x) 
  | otherwise 
  = Use t

getSrcSpan' x 
  | loc == noSrcSpan
  = traceShow ("myGetSrcSpan: No Location for: " ++ showPpr x) $ loc
  | otherwise
  = loc
  where loc = getSrcSpan x

-----------------------------------------------------------------------
---------- Helpers: Creating Fresh Refinement ------------------ ------
-----------------------------------------------------------------------

truePredRef :: (PPrint r, F.Reftable r) => PVar (RRType r) -> CG SpecType
truePredRef (PV _ τ _)
  = trueTy (toType τ)

freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG (Ref RSort RReft SpecType)
freshPredRef γ e (PV n τ as)
  = do t    <- freshTy_type PredInstE e (toType τ)
       args <- mapM (\_ -> fresh) as
       let targs = zip args (fst3 <$> as)
       γ' <- foldM (++=) γ [("freshPredRef", x, ofRSort τ) | (x, τ) <- targs]
       addW $ WfC γ' t
       return $ RPoly targs t

-----------------------------------------------------------------------
---------- Helpers: Creating Refinement Types For Various Things ------
-----------------------------------------------------------------------

argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr _ (Var vy)    = Just $ F.eVar vy
argExpr γ (Lit c)     = snd  $ literalConst (emb γ) c
argExpr γ (Tick _ e)  = argExpr γ e
argExpr _ e           = errorstar $ "argExpr: " ++ showPpr e


varRefType γ x = liftM (varRefType' γ x) (γ ??= F.symbol x)

varRefType' γ x t'
  | Just tys <- trec γ 
  = maybe t (`strengthen` xr) (x' `M.lookup` tys)
  | otherwise
  = t
  where t  = t' `strengthen` xr
        xr = singletonReft x -- uTop $ F.symbolReft $ F.symbol x
        x' = F.symbol x

-- TODO: should only expose/use subt. Not subsTyVar_meet
subsTyVar_meet' (α, t) = subsTyVar_meet (α, toRSort t, t)

-----------------------------------------------------------------------
--------------- Forcing Strictness ------------------------------------
-----------------------------------------------------------------------

instance NFData CGEnv where
  rnf (CGE x1 x2 x3 x4 x5 x6 x7 x8 _ x9 x10 _ _) 
    = x1 `seq` rnf x2 `seq` seq x3 `seq` x4 `seq` rnf x5 `seq` 
      rnf x6  `seq` x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10

instance NFData FEnv where
  rnf (FE x1 _) = rnf x1

instance NFData SubC where
  rnf (SubC x1 x2 x3) 
    = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (SubR x1 x2) 
    = rnf x1 `seq` rnf x2

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
          ({-# SCC "CGIrnf10" #-} rnf (lits x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kvProf x)) 

-------------------------------------------------------------------------------
--------------------- Reftypes from F.Fixpoint Expressions ----------------------
-------------------------------------------------------------------------------

forallExprRefType     :: CGEnv -> SpecType -> SpecType
forallExprRefType γ t = t `strengthen` (uTop r') 
  where r'            = fromMaybe F.top $ forallExprReft γ r 
        r             = F.sr_reft $ rTypeSortedReft (emb γ) t

forallExprReft γ r 
  = do e  <- F.isSingletonReft r
       r' <- forallExprReft_ γ e
       return r'

forallExprReft_ γ e@(F.EApp f es) 
  = case forallExprReftLookup γ f of
      Just (xs,_,t) -> let su = F.mkSubst $ safeZip "fExprRefType" xs es in
                       Just $ F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing -- F.exprReft e

forallExprReft_ γ e@(F.EVar x) 
  = case forallExprReftLookup γ x of 
      Just (_,_,t)  -> Just $ F.sr_reft $ rTypeSortedReft (emb γ) t 
      Nothing       -> Nothing -- F.exprReft e

forallExprReft_ _ e = Nothing -- F.exprReft e 

forallExprReftLookup γ x = snap <$> F.lookupSEnv x (syenv γ)
  where 
    snap                 = bkArrow . thd3 . bkUniv . (γ ?=) . F.symbol

grapBindsWithType tx γ 
  = fst <$> toListREnv (filterREnv ((== toRSort tx) . toRSort) (renv γ))

splitExistsCases z xs tx
  = fmap $ fmap (exrefAddEq z xs tx)

exrefAddEq z xs t (F.Reft(s, rs))
  = F.Reft(s, [F.RConc (F.POr [ pand x | x <- xs])])
  where tref                = fromMaybe F.top $ stripRTypeBase t
        pand x              = F.PAnd $ (substzx x) (fFromRConc <$> rs)
                                       ++ exrefToPred x tref
        substzx x           = F.subst (F.mkSubst [(z, F.EVar x)])

exrefToPred x uref
  = F.subst (F.mkSubst [(v, F.EVar x)]) ((fFromRConc <$> r))
  where (F.Reft(v, r))         = ur_reft uref
fFromRConc (F.RConc p) = p
fFromRConc _           = errorstar "can not hanlde existential type with kvars"

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
  = rFun (F.symbol x) (ofType $ varType x) (exprRefType_ γ e)

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
--------- | Strengthening Binders with TyCon Invariants -----------
-------------------------------------------------------------------

type RTyConInv = M.HashMap RTyCon [SpecType]

-- mkRTyConInv    :: [Located SpecType] -> RTyConInv 
mkRTyConInv ts = group [ (c, t) | t@(RApp c _ _ _) <- strip <$> ts]
  where 
    strip      = thd3 . bkUniv . val 

addRTyConInv :: RTyConInv -> SpecType -> SpecType
addRTyConInv m t@(RApp c _ _ _)
  = case M.lookup c m of
      Nothing -> t
      Just ts -> foldl' conjoinInvariant' t ts
addRTyConInv _ t 
  = t 

conjoinInvariant' t1 t2     
  = conjoinInvariantShift t1 t2

conjoinInvariantShift t1 t2 
  = conjoinInvariant t1 (shiftVV t2 (rTypeValueVar t1)) 

conjoinInvariant (RApp c ts rs r) (RApp ic its _ ir) 
  | (c == ic && length ts == length its)
  = RApp c (zipWith conjoinInvariantShift ts its) rs (r `F.meet` ir)

conjoinInvariant t@(RApp _ _ _ r) (RVar _ ir) 
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t@(RVar _ r) (RVar _ ir) 
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t _  
  = t

---------------------------------------------------------------
----- Refinement Type Environments ----------------------------
---------------------------------------------------------------

newtype REnv = REnv  (M.HashMap F.Symbol SpecType) -- deriving (Data, Typeable)

instance PPrint REnv where
  pprint (REnv m)  = vcat $ map pprxt $ M.toList m
    where 
      pprxt (x, t) = pprint x <> dcolon <> pprint t  

instance NFData REnv where
  rnf (REnv _) = () -- rnf m

toListREnv (REnv env)     = M.toList env
filterREnv f (REnv env)   = REnv $ M.filter f env
fromListREnv              = REnv . M.fromList
deleteREnv x (REnv env)   = REnv (M.delete x env)
insertREnv x y (REnv env) = REnv (M.insert x y env)
lookupREnv x (REnv env)   = M.lookup x env
memberREnv x (REnv env)   = M.member x env
-- domREnv (REnv env)        = M.keys env
-- emptyREnv                 = REnv M.empty

cgInfoFInfoBot cgi = cgInfoFInfo cgi { specQuals = [] }

cgInfoFInfoKvars cgi kvars = cgInfoFInfo cgi{fixCs = fixCs' ++ trueCs}
  where fixCs' = concatMap (updateCs kvars) (fixCs cgi) 
        trueCs = (`F.trueSubCKvar` (Ci noSrcSpan Nothing)) <$> kvars

cgInfoFInfo cgi
  = F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
         , F.ws    = fixWfs cgi  
         , F.bs    = binds cgi 
         , F.gs    = globals cgi 
         , F.lits  = lits cgi 
         , F.kuts  = kuts cgi 
         , F.quals = specQuals cgi
         }

updateCs kvars cs
  | null lhskvars || F.isFalse rhs
  = [cs] 
  | all (`elem` kvars) lhskvars && null lhsconcs
  = []
  | any (`elem` kvars) lhskvars
  = [F.removeLhsKvars cs kvars]
  | otherwise 
  = [cs]
  where lhskvars = F.reftKVars lhs
        rhskvars = F.reftKVars rhs
        lhs      = F.lhsCs cs
        rhs      = F.rhsCs cs
        F.Reft(_, lhspds) = lhs
        lhsconcs = [p | F.RConc p <- lhspds]

