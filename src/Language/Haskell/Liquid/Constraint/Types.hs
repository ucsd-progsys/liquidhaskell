module Language.Haskell.Liquid.Constraint.Types  where

import CoreSyn
import SrcLoc           


import qualified TyCon   as TC
import qualified DataCon as DC


import Text.PrettyPrint.HughesPJ hiding (first)



import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T


import Control.Applicative      ((<$>))
import Data.Monoid              (mconcat)
import Data.Maybe               (catMaybes)

import Var

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc     (fourth4)
import Language.Haskell.Liquid.RefType  (shiftVV)
import Language.Haskell.Liquid.PredType (wiredSortedSyms)
import qualified Language.Fixpoint.Types            as F

import Language.Fixpoint.Misc 



import qualified Language.Haskell.Liquid.CTags      as Tg


import Language.Haskell.Liquid.Strata


------------------------------------------------------------------------------
------------------------------------------------------------------------------
----------------------------- Helper Types: HEnv -----------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------



newtype HEnv = HEnv (S.HashSet F.Symbol)

fromListHEnv = HEnv . S.fromList
elemHEnv x (HEnv s) = x `S.member` s





------------------------------------------------------------------------------
------------------------------------------------------------------------------
-------------------------- Helper Types: Invariants --------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------


type RTyConInv = M.HashMap RTyCon [SpecType]
type RTyConIAl = M.HashMap RTyCon [SpecType]

mkRTyConInv    :: [F.Located SpecType] -> RTyConInv 
mkRTyConInv ts = group [ (c, t) | t@(RApp c _ _ _) <- strip <$> ts]
  where 
    strip      = fourth4 . bkUniv . val 

mkRTyConIAl    = mkRTyConInv . fmap snd

addRTyConInv :: RTyConInv -> SpecType -> SpecType
addRTyConInv m t@(RApp c _ _ _)
  = case M.lookup c m of
      Nothing -> t
      Just ts -> L.foldl' conjoinInvariant' t ts
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
     xs  = ty_args $ toRTypeRep t

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
        -- , penv   :: !(F.SEnv PrType)   -- ^ PrTypes for top-level bindings (merge with renv) 
        , fenv   :: !FEnv              -- ^ Fixpoint Environment
        , recs   :: !(S.HashSet Var)   -- ^ recursive defs being processed (for annotations)
        , invs   :: !RTyConInv         -- ^ Datatype invariants 
        , ial    :: !RTyConIAl         -- ^ Datatype checkable invariants 
        , grtys  :: !REnv              -- ^ Top-level variables with (assert)-guarantees to verify
        , assms  :: !REnv              -- ^ Top-level variables with assumed types
        , emb    :: F.TCEmb TC.TyCon   -- ^ How to embed GHC Tycons into fixpoint sorts
        , tgEnv :: !Tg.TagEnv          -- ^ Map from top-level binders to fixpoint tag
        , tgKey :: !(Maybe Tg.TagKey)  -- ^ Current top-level binder
        , trec  :: !(Maybe (M.HashMap F.Symbol SpecType)) -- ^ Type of recursive function with decreasing constraints
        , lcb   :: !(M.HashMap F.Symbol CoreExpr) -- ^ Let binding that have not been checked
        , holes :: !HEnv               -- ^ Types with holes, will need refreshing
        } -- deriving (Data, Typeable)

instance PPrint CGEnv where
  pprint = pprint . renv

instance Show CGEnv where
  show = showpp



-----------------------------------------------------------------
------------------- Constraints: Types --------------------------
-----------------------------------------------------------------

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
  pprint c = pprint (senv c)
           $+$ ((text " |- ") <+> ( (pprint (lhs c)) 
                             $+$ text "<:" 
                             $+$ (pprint (rhs c))))

instance PPrint WfC where
  pprint (WfC w r) = pprint w <> text " |- " <> pprint r 

instance SubStratum SubC where
  subS su (SubC γ t1 t2) = SubC γ (subS su t1) (subS su t2)
  subS _  c              = c




-----------------------------------------------------------
-------------------- Generation: Types --------------------
-----------------------------------------------------------

data CGInfo = CGInfo { hsCs       :: ![SubC]                      -- ^ subtyping constraints over RType
                     , hsWfs      :: ![WfC]                       -- ^ wellformedness constraints over RType
                     , sCs        :: ![SubC]                      -- ^ additional stratum constrains for let bindings
                     , fixCs      :: ![FixSubC]                   -- ^ subtyping over Sort (post-splitting)
                     , isBind     :: ![Bool]                      -- ^ tracks constraints that come from let-bindings 
                     , fixWfs     :: ![FixWfC]                    -- ^ wellformedness constraints over Sort (post-splitting)
                     , globals    :: !F.FEnv                      -- ^ ? global measures
                     , freshIndex :: !Integer                     -- ^ counter for generating fresh KVars
                     , binds      :: !F.BindEnv                   -- ^ set of environment binders
                     , annotMap   :: !(AnnInfo (Annot SpecType))  -- ^ source-position annotation map
                     , tyConInfo  :: !(M.HashMap TC.TyCon RTyCon) -- ^ information about type-constructors
                     , specQuals  :: ![F.Qualifier]               -- ^ ? qualifiers in source files
                     , specDecr   :: ![(Var, [Int])]              -- ^ ? FIX THIS
                     , termExprs  :: !(M.HashMap Var [F.Expr])    -- ^ Terminating Metrics for Recursive functions
                     , specLVars  :: !(S.HashSet Var)             -- ^ Set of variables to ignore for termination checking
                     , specLazy   :: !(S.HashSet Var)             -- ^ ? FIX THIS
                     , tyConEmbed :: !(F.TCEmb TC.TyCon)          -- ^ primitive Sorts into which TyCons should be embedded
                     , kuts       :: !(F.Kuts)                    -- ^ Fixpoint Kut variables (denoting "back-edges"/recursive KVars)
                     , lits       :: ![(F.Symbol, F.Sort)]        -- ^ ? FIX THIS 
                     , tcheck     :: !Bool                        -- ^ Check Termination (?) 
                     , scheck     :: !Bool                        -- ^ Check Strata (?)
                     , trustghc   :: !Bool                        -- ^ Trust ghc auto generated bindings
                     , pruneRefs  :: !Bool                        -- ^ prune unsorted refinements
                     , logErrors  :: ![TError SpecType]           -- ^ Errors during coontraint generation
                     , kvProf     :: !KVProf                      -- ^ Profiling distribution of KVars 
                     , recCount   :: !Int                         -- ^ number of recursive functions seen (for benchmarks)
                     } -- deriving (Data, Typeable)

instance PPrint CGInfo where 
  pprint cgi =  {-# SCC "ppr_CGI" #-} ppr_CGInfo cgi

ppr_CGInfo cgi 
  =  (text "*********** Constraint Information ***********")
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

