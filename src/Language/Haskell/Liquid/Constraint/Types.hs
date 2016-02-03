
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}

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

   -- * Hole Environment
  , HEnv
  , fromListHEnv
  , elemHEnv

   -- * Subtyping Constraints
  , SubC (..)
  , FixSubC

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
  ) where

import Prelude hiding (error)
import CoreSyn
import SrcLoc

import qualified TyCon   as TC
import qualified DataCon as DC


import Text.PrettyPrint.HughesPJ hiding (first)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L

import Control.DeepSeq
-- import Data.Monoid              (mconcat)
import Data.Maybe               (catMaybes)
import Control.Monad.State


import Var
import Type   (Type)
import Class  (Class)

import Language.Haskell.Liquid.GHC.Misc (showPpr)

import Language.Haskell.Liquid.GHC.SpanStack
import Language.Haskell.Liquid.Types hiding   (binds)
import Language.Haskell.Liquid.Types.Strata
import Language.Haskell.Liquid.Misc           (fourth4)
import Language.Haskell.Liquid.Types.RefType  (shiftVV)
import Language.Haskell.Liquid.WiredIn        (wiredSortedSyms)
import qualified Language.Fixpoint.Types            as F

import Language.Fixpoint.Misc

import qualified Language.Haskell.Liquid.UX.CTags      as Tg

type CG = State CGInfo

data CGEnv
  = CGE { cgLoc  :: !SpanStack         -- ^ Location in original source file
        , renv   :: !REnv              -- ^ SpecTypes for Bindings in scope
        , syenv  :: !(F.SEnv Var)      -- ^ Map from free Symbols (e.g. datacons) to Var
        , denv   :: !RDEnv             -- ^ Dictionary Environment
        , fenv   :: !FEnv              -- ^ Fixpoint Environment
        , recs   :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
        , invs   :: !RTyConInv         -- ^ Datatype invariants
        , ial    :: !RTyConIAl         -- ^ Datatype checkable invariants
        , grtys  :: !REnv              -- ^ Top-level variables with (assert)-guarantees to verify
        , assms  :: !REnv              -- ^ Top-level variables with assumed types
        , emb    :: F.TCEmb TC.TyCon   -- ^ How to embed GHC Tycons into fixpoint sorts
        , tgEnv :: !Tg.TagEnv          -- ^ Map from top-level binders to fixpoint tag
        , tgKey :: !(Maybe Tg.TagKey)                     -- ^ Current top-level binder
        , trec  :: !(Maybe (M.HashMap F.Symbol SpecType)) -- ^ Type of recursive function with decreasing constraints
        , lcb   :: !(M.HashMap F.Symbol CoreExpr)         -- ^ Let binding that have not been checked (c.f. LAZYVARs)
        , holes :: !HEnv                                  -- ^ Types with holes, will need refreshing
        , lcs   :: !LConstraint                           -- ^ Logical Constraints
        , aenv  :: !(M.HashMap Var F.Symbol)              -- ^ axiom environment maps axiomatized Haskell functions to the logical functions
        } -- deriving (Data, Typeable)

data LConstraint = LC [[(F.Symbol, SpecType)]]

instance Monoid LConstraint where
  mempty  = LC []
  mappend (LC cs1) (LC cs2) = LC (cs1 ++ cs2)


instance PPrint CGEnv where
  pprint = pprint . renv

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

instance PPrint SubC where
  -- pprint c = pprint (senv c)
  --           $+$ (text " |- " <+> (pprint (lhs c) $+$
  --                                 text "<:"      $+$
  --                                 pprint (rhs c)))
  pprint c@(SubC {}) = pprint (senv c)
                       $+$ ("||-" <+> vcat [ pprint (lhs c)
                                           , "<:"
                                           , pprint (rhs c) ] )
  pprint c@(SubR {}) = pprint (senv c)
                       $+$ ("||-" <+> vcat [ pprint (ref c)
                                           , parens (pprint (oblig c))])


instance PPrint WfC where
  pprint (WfC _ r) = {- pprint w <> text -} "<...> |-" <+> pprint r

instance SubStratum SubC where
  subS su (SubC γ t1 t2) = SubC γ (subS su t1) (subS su t2)
  subS _  c              = c

--------------------------------------------------------------------------------
-- | Generation: Types ---------------------------------------------------------
--------------------------------------------------------------------------------

data CGInfo = CGInfo {
    fEnv       :: !(F.SEnv F.Sort)             -- ^ top-level fixpoint env
  , hsCs       :: ![SubC]                      -- ^ subtyping constraints over RType
  , hsWfs      :: ![WfC]                       -- ^ wellformedness constraints over RType
  , sCs        :: ![SubC]                      -- ^ additional stratum constrains for let bindings
  , fixCs      :: ![FixSubC]                   -- ^ subtyping over Sort (post-splitting)
  , isBind     :: ![Bool]                      -- ^ tracks constraints that come from let-bindings
  , fixWfs     :: ![FixWfC]                    -- ^ wellformedness constraints over Sort (post-splitting)
  , freshIndex :: !Integer                     -- ^ counter for generating fresh KVars
  , binds      :: !F.BindEnv                   -- ^ set of environment binders
  , annotMap   :: !(AnnInfo (Annot SpecType))  -- ^ source-position annotation map
  , tyConInfo  :: !(M.HashMap TC.TyCon RTyCon) -- ^ information about type-constructors
  , specDecr   :: ![(Var, [Int])]              -- ^ ? FIX THIS
  , termExprs  :: !(M.HashMap Var [F.Expr])    -- ^ Terminating Metrics for Recursive functions
  , specLVars  :: !(S.HashSet Var)             -- ^ Set of variables to ignore for termination checking
  , specLazy   :: !(S.HashSet Var)             -- ^ ? FIX THIS
  , autoSize   :: !(S.HashSet TC.TyCon)        -- ^ ? FIX THIS
  , tyConEmbed :: !(F.TCEmb TC.TyCon)          -- ^ primitive Sorts into which TyCons should be embedded
  , kuts       :: !F.Kuts                      -- ^ Fixpoint Kut variables (denoting "back-edges"/recursive KVars)
  , lits       :: ![(F.Symbol, F.Sort)]        -- ^ ? FIX THIS
  , tcheck     :: !Bool                        -- ^ Check Termination (?)
  , scheck     :: !Bool                        -- ^ Check Strata (?)
  , trustghc   :: !Bool                        -- ^ Trust ghc auto generated bindings
  , pruneRefs  :: !Bool                        -- ^ prune unsorted refinements
  , logErrors  :: ![Error]                     -- ^ Errors during constraint generation
  , kvProf     :: !KVProf                      -- ^ Profiling distribution of KVars
  , recCount   :: !Int                         -- ^ number of recursive functions seen (for benchmarks)
  , bindSpans  :: M.HashMap F.BindId SrcSpan   -- ^ Source Span associated with Fixpoint Binder
  }

instance PPrint CGInfo where
  pprint cgi =  {-# SCC "ppr_CGI" #-} pprCGInfo cgi

pprCGInfo _cgi
  =  text "*********** Constraint Information ***********"
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
  -- -$$ (text "*********** Literals in Source     ************")
  -- -$$ (pprint $ lits cgi)
  -- -$$ (text "*********** KVar Distribution *****************")
  -- -$$ (pprint $ kvProf cgi)
  -- -$$ (text "Recursive binders:" <+> pprint (recCount cgi))


--------------------------------------------------------------------------------
-- | Helper Types: HEnv --------------------------------------------------------
--------------------------------------------------------------------------------

newtype HEnv = HEnv (S.HashSet F.Symbol)

fromListHEnv = HEnv . S.fromList
elemHEnv x (HEnv s) = x `S.member` s

--------------------------------------------------------------------------------
-- | Helper Types: Invariants --------------------------------------------------
--------------------------------------------------------------------------------

type RTyConInv = M.HashMap RTyCon [SpecType]
type RTyConIAl = M.HashMap RTyCon [SpecType]

--------------------------------------------------------------------------------
mkRTyConInv    :: [F.Located SpecType] -> RTyConInv
--------------------------------------------------------------------------------
mkRTyConInv ts = group [ (c, t) | t@(RApp c _ _ _) <- strip <$> ts]
  where
    strip      = fourth4 . bkUniv . val

mkRTyConIAl    = mkRTyConInv . fmap snd

addRTyConInv :: RTyConInv -> SpecType -> SpecType
addRTyConInv m t@(RApp c _ _ _)
  = case M.lookup c m of
      Nothing -> t
      Just ts -> L.foldl' conjoinInvariantShift  t ts
addRTyConInv _ t
  = t

addRInv :: RTyConInv -> (Var, SpecType) -> (Var, SpecType)
addRInv m (x, t)
  | x `elem` ids , (RApp c _ _ _) <- res t, Just invs <- M.lookup c m
  = (x, addInvCond t (mconcat $ catMaybes (stripRTypeBase <$> invs)))
  | otherwise
  = (x, t)
   where
     ids = [id | tc <- M.keys m
               , dc <- TC.tyConDataCons $ rtc_tc tc
               , id <- DC.dataConImplicitIds dc]
     res = ty_res . toRTypeRep

conjoinInvariantShift t1 t2
  = conjoinInvariant t1 (shiftVV t2 (rTypeValueVar t1))

conjoinInvariant (RApp c ts rs r) (RApp ic its _ ir)
  | c == ic && length ts == length its
  = RApp c (zipWith conjoinInvariantShift ts its) rs (r `F.meet` ir)

conjoinInvariant t@(RApp _ _ _ r) (RVar _ ir)
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t@(RVar _ r) (RVar _ ir)
  = t { rt_reft = r `F.meet` ir }

conjoinInvariant t _
  = t

--------------------------------------------------------------------------------
-- | Fixpoint Environment ------------------------------------------------------
--------------------------------------------------------------------------------

data FEnv = FE { feBinds :: !F.IBindEnv      -- ^ Integer Keys for Fixpoint Environment
               , feEnv   :: !(F.SEnv F.Sort) -- ^ Fixpoint Environment
               }

insertFEnv (FE benv env) ((x, t), i)
  = FE (F.insertsIBindEnv [i] benv) (F.insertSEnv x t env)

insertsFEnv :: FEnv -> [((F.Symbol, F.Sort), F.BindId)] -> FEnv
insertsFEnv = L.foldl' insertFEnv

initFEnv xts = FE F.emptyIBindEnv $ F.fromListSEnv (wiredSortedSyms ++ xts)

--------------------------------------------------------------------------------
-- | Forcing Strictness --------------------------------------------------------
--------------------------------------------------------------------------------

instance NFData CGEnv where
  rnf (CGE x1 _ x3 _ x5 x6 x7 x8 x9 _ _ x10 _ _ _ _ _ _)
    = x1 `seq` {- rnf x2 `seq` -} seq x3 `seq` rnf x5 `seq`
      rnf x6  `seq` x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10

instance NFData FEnv where
  rnf (FE x1 _) = rnf x1

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
          ({-# SCC "CGIrnf10" #-} rnf (lits x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kvProf x))
