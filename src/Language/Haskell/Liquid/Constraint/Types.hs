{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}


module Language.Haskell.Liquid.Constraint.Types
  ( -- * Constraint Generation Monad
    CG

    -- * Constraint information
  , CGInfo (..)

    -- * Constraint Generation Environment
  , CGEnv (..)

    -- * Logical constraints (FIXME: related to bounds?)
  , LConstraint (..)

    -- * Fixpoint environment
  , FEnv (..)
  , initFEnv
  , insertsFEnv
  -- , removeFEnv

   -- * Hole Environment
  , HEnv
  , fromListHEnv
  , elemHEnv

   -- * Subtyping Constraints
  , SubC (..)
  , FixSubC

  , subVar

   -- * Well-formedness Constraints
  , WfC (..)
  , FixWfC

   -- * Invariants
  , RTyConInv
  , mkRTyConInv
  , addRTyConInv
  , addRInv

  -- * Aliases?
  , RTyConIAl
  , mkRTyConIAl

  , removeInvariant, restoreInvariant, makeRecInvariants

  , addArgument, addArguments

  , getTemplates
  ) where

import Prelude hiding (error)
import           CoreSyn
import           Type (TyThing( AnId ))
import           Var
import           SrcLoc
import           Unify (tcUnifyTy)
import qualified TyCon   as TC
import qualified DataCon as DC
import           Text.PrettyPrint.HughesPJ hiding ((<>)) 
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import           Control.DeepSeq
import           Data.Maybe               (catMaybes, isJust)
import           Control.Monad.State
-- import           Control.Monad.Fail 

import           Language.Haskell.Liquid.GHC.SpanStack
import           Language.Haskell.Liquid.Types hiding   (binds)
-- import           Language.Haskell.Liquid.Types.Strata
import           Language.Haskell.Liquid.Misc           (fourth4)
-- import           Language.Haskell.Liquid.Types.RefType  (shiftVV, toType)
import           Language.Haskell.Liquid.WiredIn        (wiredSortedSyms)
import qualified Language.Fixpoint.Types            as F
import Language.Fixpoint.Misc

import qualified Language.Haskell.Liquid.UX.CTags      as Tg

type CG = State CGInfo

data CGEnv = CGE
  { cgLoc    :: !SpanStack         -- ^ Location in original source file
  , renv     :: !REnv              -- ^ SpecTypes for Bindings in scope
  , syenv    :: !(F.SEnv Var)      -- ^ Map from free Symbols (e.g. datacons) to Var
  , denv     :: !RDEnv             -- ^ Dictionary Environment
  , litEnv   :: !(F.SEnv F.Sort)   -- ^ Global  literals
  , constEnv :: !(F.SEnv F.Sort)   -- ^ Distinct literals
  , fenv   :: !FEnv              -- ^ Fixpoint Environment
  , recs   :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
  , fargs  :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
  , invs   :: !RTyConInv         -- ^ Datatype invariants
  , rinvs  :: !RTyConInv         -- ^ Datatype recursive invariants: ignored in the base case assumed in rec call
  , ial    :: !RTyConIAl         -- ^ Datatype checkable invariants
  , grtys  :: !REnv              -- ^ Top-level variables with (assert)-guarantees to verify
  , assms  :: !REnv              -- ^ Top-level variables with assumed types
  , intys  :: !REnv              -- ^ Top-level variables with auto generated internal types
  , emb    :: F.TCEmb TC.TyCon   -- ^ How to embed GHC Tycons into fixpoint sorts
  , tgEnv  :: !Tg.TagEnv          -- ^ Map from top-level binders to fixpoint tag
  , tgKey  :: !(Maybe Tg.TagKey)                     -- ^ Current top-level binder
  , trec   :: !(Maybe (M.HashMap F.Symbol SpecType)) -- ^ Type of recursive function with decreasing constraints
  , lcb    :: !(M.HashMap F.Symbol CoreExpr)         -- ^ Let binding that have not been checked (c.f. LAZYVARs)
  , forallcb :: !(M.HashMap Var F.Expr)              -- ^ Polymorhic let bindings 
  , holes  :: !HEnv                                  -- ^ Types with holes, will need refreshing
  , lcs    :: !LConstraint                           -- ^ Logical Constraints
  , aenv   :: !(M.HashMap Var F.Symbol)              -- ^ axiom environment maps reflected Haskell functions to the logical functions
  , cerr   :: !(Maybe (TError SpecType))             -- ^ error that should be reported at the user
  -- , cgCfg  :: !Config                                -- ^ top-level config options
  , cgInfo :: !GhcInfo                               -- ^ top-level GhcInfo
  , cgVar  :: !(Maybe Var)                           -- ^ top level function being checked
  } -- deriving (Data, Typeable)

instance HasConfig CGEnv where
  getConfig = getConfig . cgInfo

data LConstraint = LC [[(F.Symbol, SpecType)]]

instance Monoid LConstraint where
  mempty  = LC []
  mappend = (<>)

instance Semigroup LConstraint where
  LC cs1 <> LC cs2 = LC (cs1 ++ cs2)

instance PPrint CGEnv where
  pprintTidy k = pprintTidy k . renv

instance Show CGEnv where
  show = showpp

--------------------------------------------------------------------------------
-- | Subtyping Constraints -----------------------------------------------------
--------------------------------------------------------------------------------

-- RJ: what is the difference between these two?

data SubC     = SubC { senv  :: !CGEnv
                     , lhs   :: !SpecType
                     , rhs   :: !SpecType
                     }
              | SubR { senv  :: !CGEnv
                     , oblig :: !Oblig
                     , ref   :: !RReft
                     }

data WfC      = WfC  !CGEnv !SpecType
              -- deriving (Data, Typeable)

type FixSubC  = F.SubC Cinfo
type FixWfC   = F.WfC Cinfo


subVar :: FixSubC -> Maybe Var
subVar = ci_var . F.sinfo

instance PPrint SubC where
  pprintTidy k c@(SubC {}) = pprintTidy k (senv c)
                             $+$ ("||-" <+> vcat [ pprintTidy k (lhs c)
                                                 , "<:"
                                                 , pprintTidy k (rhs c) ] )
  pprintTidy k c@(SubR {}) = pprintTidy k (senv c)
                             $+$ ("||-" <+> vcat [ pprintTidy k (ref c)
                                                 , parens (pprintTidy k (oblig c))])


instance PPrint WfC where
  pprintTidy k (WfC _ r) = {- pprintTidy k w <> text -} "<...> |-" <+> pprintTidy k r


instance SubStratum SubC where
  subS su (SubC γ t1 t2) = SubC γ (subS su t1) (subS su t2)
  subS _  c              = c

--------------------------------------------------------------------------------
-- | Generation: Types ---------------------------------------------------------
--------------------------------------------------------------------------------
data CGInfo = CGInfo 
  { fEnv       :: !(F.SEnv F.Sort)             -- ^ top-level fixpoint env
  , hsCs       :: ![SubC]                      -- ^ subtyping constraints over RType
  , hsWfs      :: ![WfC]                       -- ^ wellformedness constraints over RType
  , sCs        :: ![SubC]                      -- ^ additional stratum constrains for let bindings
  , fixCs      :: ![FixSubC]                   -- ^ subtyping over Sort (post-splitting)
  , isBind     :: ![Bool]                      -- ^ tracks constraints that come from let-bindings
  , fixWfs     :: ![FixWfC]                    -- ^ wellformedness constraints over Sort (post-splitting)
  , freshIndex :: !Integer                     -- ^ counter for generating fresh KVars
  , binds      :: !F.BindEnv                   -- ^ set of environment binders
  , ebinds     :: ![F.BindId]                  -- ^ existentials
  , annotMap   :: !(AnnInfo (Annot SpecType))  -- ^ source-position annotation map
  , holesMap   :: !(M.HashMap Var [HoleInfo SpecType])    -- ^ information for ghc hole expressions
  , tyConInfo  :: !TyConMap                    -- ^ information about type-constructors
  , specDecr   :: ![(Var, [Int])]              -- ^ ^ Lexicographic order of decreasing args (DEPRECATED) 
  , newTyEnv   :: !(M.HashMap TC.TyCon SpecType)        -- ^ Mapping of new type type constructors with their refined types.
  , termExprs  :: !(M.HashMap Var [F.Located F.Expr])   -- ^ Terminating Metrics for Recursive functions
  , specLVars  :: !(S.HashSet Var)             -- ^ Set of variables to ignore for termination checking
  , specLazy   :: !(S.HashSet Var)             -- ^ "Lazy binders", skip termination checking
  , specTmVars :: !(S.HashSet Var)             -- ^ Binders that FAILED struct termination check that MUST be checked 
  , autoSize   :: !(S.HashSet TC.TyCon)        -- ^ ? FIX THIS
  , tyConEmbed :: !(F.TCEmb TC.TyCon)          -- ^ primitive Sorts into which TyCons should be embedded
  , kuts       :: !F.Kuts                      -- ^ Fixpoint Kut variables (denoting "back-edges"/recursive KVars)
  , kvPacks    :: ![S.HashSet F.KVar]          -- ^ Fixpoint "packs" of correlated kvars
  , cgLits     :: !(F.SEnv F.Sort)             -- ^ Global symbols in the refinement logic
  , cgConsts   :: !(F.SEnv F.Sort)             -- ^ Distinct constant symbols in the refinement logic
  , cgADTs     :: ![F.DataDecl]                -- ^ ADTs extracted from Haskell 'data' definitions
  , tcheck     :: !Bool                        -- ^ Check Termination (?)
  , scheck     :: !Bool                        -- ^ Check Strata (?)
  , pruneRefs  :: !Bool                        -- ^ prune unsorted refinements
  , logErrors  :: ![Error]                     -- ^ Errors during constraint generation
  , kvProf     :: !KVProf                      -- ^ Profiling distribution of KVars
  , recCount   :: !Int                         -- ^ number of recursive functions seen (for benchmarks)
  , bindSpans  :: M.HashMap F.BindId SrcSpan   -- ^ Source Span associated with Fixpoint Binder
  , allowHO    :: !Bool
  , ghcI       :: !GhcInfo
  , dataConTys :: ![(Var, SpecType)]           -- ^ Refined Types of Data Constructors
  , unsorted   :: !F.Templates                 -- ^ Potentially unsorted expressions
  }


getTemplates :: CG F.Templates
getTemplates = do 
  fg     <- pruneRefs <$> get
  ts     <- unsorted  <$> get
  return $ if fg then F.anything else ts 
       

instance PPrint CGInfo where
  pprintTidy = pprCGInfo

pprCGInfo :: F.Tidy -> CGInfo -> Doc
pprCGInfo _k _cgi
  =  "*********** Constraint Information (omitted) *************"
  -- -$$ (text "*********** Haskell SubConstraints ***********")
  -- -$$ (pprintLongList $ hsCs  cgi)
  -- -$$ (text "*********** Haskell WFConstraints ************")
  -- -$$ (pprintLongList $ hsWfs cgi)
  -- -$$ (text "*********** Fixpoint SubConstraints **********")
  -- -$$ (F.toFix  $ fixCs cgi)
  -- -$$ (text "*********** Fixpoint WFConstraints ************")
  -- -$$ (F.toFix  $ fixWfs cgi)
  -- -$$ (text "*********** Fixpoint Kut Variables ************")
  -- -$$ (F.toFix  $ kuts cgi)
  -- -$$ "*********** Literals in Source     ************"
  -- -$$ F.pprint (cgLits _cgi)
  -- -$$ (text "*********** KVar Distribution *****************")
  -- -$$ (pprint $ kvProf cgi)
  -- -$$ (text "Recursive binders:" <+> pprint (recCount cgi))


--------------------------------------------------------------------------------
-- | Helper Types: HEnv --------------------------------------------------------
--------------------------------------------------------------------------------

newtype HEnv = HEnv (S.HashSet F.Symbol)

fromListHEnv :: [F.Symbol] -> HEnv
fromListHEnv = HEnv . S.fromList

elemHEnv :: F.Symbol -> HEnv -> Bool
elemHEnv x (HEnv s) = x `S.member` s

--------------------------------------------------------------------------------
-- | Helper Types: Invariants --------------------------------------------------
--------------------------------------------------------------------------------
data RInv = RInv { _rinv_args :: [RSort]   -- empty list means that the invariant is generic
                                           -- for all type arguments
                 , _rinv_type :: SpecType
                 , _rinv_name :: Maybe Var
                 } deriving Show

type RTyConInv = M.HashMap RTyCon [RInv]
type RTyConIAl = M.HashMap RTyCon [RInv]


addArgument :: CGEnv -> Var -> CGEnv
addArgument γ v
 | higherOrderFlag γ
 = γ {fargs = S.insert v (fargs γ) }
 | otherwise
 = γ

addArguments :: CGEnv -> [Var] -> CGEnv
addArguments γ vs
 | higherOrderFlag γ
 = foldl addArgument γ vs
 | otherwise
 = γ

--------------------------------------------------------------------------------
mkRTyConInv    :: [(Maybe Var, F.Located SpecType)] -> RTyConInv
--------------------------------------------------------------------------------
mkRTyConInv ts = group [ (c, RInv (go ts) t v) | (v, t@(RApp c ts _ _)) <- strip <$> ts]
  where
    strip = mapSnd (fourth4 . bkUniv . val)
    go ts | generic (toRSort <$> ts) = []
          | otherwise                = toRSort <$> ts

    generic ts = let ts' = L.nub ts in
                 all isRVar ts' && length ts' == length ts

mkRTyConIAl :: [(a, F.Located SpecType)] -> RTyConInv
mkRTyConIAl    = mkRTyConInv . fmap ((Nothing,) . snd)

addRTyConInv :: RTyConInv -> SpecType -> SpecType
addRTyConInv m t
  = case lookupRInv t m of
      Nothing -> t
      Just ts -> L.foldl' conjoinInvariantShift t ts

lookupRInv :: SpecType -> RTyConInv -> Maybe [SpecType]
lookupRInv (RApp c ts _ _) m
  = case M.lookup c m of
      Nothing   -> Nothing
      Just invs -> Just (catMaybes $ goodInvs ts <$> invs)
lookupRInv _ _
  = Nothing

goodInvs :: [SpecType] -> RInv -> Maybe SpecType
goodInvs _ (RInv []  t _)
  = Just t
goodInvs ts (RInv ts' t _)
  | and (zipWith unifiable ts' (toRSort <$> ts))
  = Just t
  | otherwise
  = Nothing


unifiable :: RSort -> RSort -> Bool
unifiable t1 t2 = isJust $ tcUnifyTy (toType t1) (toType t2)

addRInv :: RTyConInv -> (Var, SpecType) -> (Var, SpecType)
addRInv m (x, t)
  | x `elem` ids , Just invs <- lookupRInv (res t) m
  = (x, addInvCond t (mconcat $ catMaybes (stripRTypeBase <$> invs)))
  | otherwise
  = (x, t)
   where
     ids = [id | tc <- M.keys m
               , dc <- TC.tyConDataCons $ rtc_tc tc
               , AnId id <- DC.dataConImplicitTyThings dc]
     res = ty_res . toRTypeRep

conjoinInvariantShift :: SpecType -> SpecType -> SpecType
conjoinInvariantShift t1 t2
  = conjoinInvariant t1 (shiftVV t2 (rTypeValueVar t1))

conjoinInvariant :: SpecType -> SpecType -> SpecType
conjoinInvariant (RApp c ts rs r) (RApp ic its _ ir)
  | c == ic && length ts == length its
  = RApp c (zipWith conjoinInvariantShift ts its) rs (r `F.meet` ir)

conjoinInvariant t@(RApp _ _ _ r) (RVar _ ir)
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t@(RVar _ r) (RVar _ ir)
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t _
  = t

removeInvariant  :: CGEnv -> CoreBind -> (CGEnv, RTyConInv)
removeInvariant γ cbs
  = (γ { invs  = M.map (filter f) (invs γ)
       , rinvs = M.map (filter (not . f)) (invs γ)}
    , invs γ)
  where
    f i | Just v  <- _rinv_name i, v `elem` binds cbs
        = False
        | otherwise
        = True
    binds (NonRec x _) = [x]
    binds (Rec xes)    = fst $ unzip xes

restoreInvariant :: CGEnv -> RTyConInv -> CGEnv
restoreInvariant γ is = γ {invs = is}

makeRecInvariants :: CGEnv -> [Var] -> CGEnv
makeRecInvariants γ [x] = γ {invs = M.unionWith (++) (invs γ) is}
  where
    is  =  M.map (map f . filter (isJust . (varType x `tcUnifyTy`) . toType . _rinv_type)) (rinvs γ)
    f i = i{_rinv_type = guard $ _rinv_type i}

    guard (RApp c ts rs r)
      | Just f <- szFun <$> sizeFunction (rtc_info c)
      = RApp c ts rs (MkUReft (ref f $ F.toReft r) mempty mempty)
      | otherwise
      = RApp c ts rs mempty
    guard t
      = t

    ref f (F.Reft(v, rr))
      = F.Reft (v, F.PImp (F.PAtom F.Lt (f v) (f $ F.symbol x)) rr)

makeRecInvariants γ _ = γ

--------------------------------------------------------------------------------
-- | Fixpoint Environment ------------------------------------------------------
--------------------------------------------------------------------------------

data FEnv = FE
  { feBinds :: !F.IBindEnv        -- ^ Integer Keys for Fixpoint Environment
  , feEnv   :: !(F.SEnv F.Sort)   -- ^ Fixpoint Environment
  , feIdEnv :: !(F.SEnv F.BindId) -- ^ Map from Symbol to current BindId
  }

insertFEnv :: FEnv -> ((F.Symbol, F.Sort), F.BindId) -> FEnv
insertFEnv (FE benv env ienv) ((x, t), i)
  = FE (F.insertsIBindEnv [i] benv)
       (F.insertSEnv x t      env)
       (F.insertSEnv x i      ienv)

insertsFEnv :: FEnv -> [((F.Symbol, F.Sort), F.BindId)] -> FEnv
insertsFEnv = L.foldl' insertFEnv

initFEnv :: [(F.Symbol, F.Sort)] -> FEnv
initFEnv xts = FE benv0 env0 ienv0
  where
    benv0    = F.emptyIBindEnv
    env0     = F.fromListSEnv (wiredSortedSyms ++ xts)
    ienv0    = F.emptySEnv

--------------------------------------------------------------------------------
-- | Forcing Strictness --------------------------------------------------------
--------------------------------------------------------------------------------
instance NFData RInv where
  rnf (RInv x y z) = rnf x `seq` rnf y `seq` rnf z

instance NFData CGEnv where
  rnf (CGE x1 _ x3 _ x4 x5 x55 x6 x7 x8 x9 _ _ _ x10 _ _ _ _ _ _ _ _ _ _ _ _)
    = x1 `seq` {- rnf x2 `seq` -} seq x3
         `seq` rnf x5
         `seq` rnf x55
         `seq` rnf x6
         `seq` x7
         `seq` rnf x8
         `seq` rnf x9
         `seq` rnf x10
         `seq` rnf x4

instance NFData FEnv where
  rnf (FE x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3

instance NFData SubC where
  rnf (SubC x1 x2 x3)
    = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (SubR x1 _ x2)
    = rnf x1 `seq` rnf x2

instance NFData WfC where
  rnf (WfC x1 x2)
    = rnf x1 `seq` rnf x2

instance NFData CGInfo where
  rnf x = ({-# SCC "CGIrnf1" #-}  rnf (hsCs x))       `seq`
          ({-# SCC "CGIrnf2" #-}  rnf (hsWfs x))      `seq`
          ({-# SCC "CGIrnf3" #-}  rnf (fixCs x))      `seq`
          ({-# SCC "CGIrnf4" #-}  rnf (fixWfs x))     `seq`
          ({-# SCC "CGIrnf6" #-}  rnf (freshIndex x)) `seq`
          ({-# SCC "CGIrnf7" #-}  rnf (binds x))      `seq`
          ({-# SCC "CGIrnf8" #-}  rnf (annotMap x))   `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kuts x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kvPacks x))    `seq`
          ({-# SCC "CGIrnf10" #-} rnf (cgLits x))     `seq`
          ({-# SCC "CGIrnf10" #-} rnf (cgConsts x))   `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kvProf x))
