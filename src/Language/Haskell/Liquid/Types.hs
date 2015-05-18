{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types (

  -- * Options
    Config (..)

  -- * Ghc Information
  , GhcInfo (..)
  , GhcSpec (..)
  , TargetVars (..)

  -- * Located Things
  , Located (..)
  , dummyLoc

  -- * Symbols
  , LocSymbol
  , LocText

  -- * Default unknown name
  , dummyName, isDummy

  -- * Refined Type Constructors
  , RTyCon (RTyCon, rtc_tc, rtc_info)
  , TyConInfo(..), defaultTyConInfo
  , rTyConPVs
  , rTyConPropVs
  , isClassRTyCon, isClassType

  -- * Refinement Types
  , RType (..), Ref(..), RTProp
  , RTyVar (..)
  , RTAlias (..)

  -- * Worlds
  , HSeg (..)
  , World (..)

  -- * Classes describing operations on `RTypes`
  , TyConable (..)
  , RefTypable (..)
  , SubsTy (..)

  -- * Predicate Variables
  , PVar (PV, pname, parg, ptype, pargs), isPropPV, pvType
  , PVKind (..)
  , Predicate (..)

  -- * Refinements
  , UReft(..)

  -- * Parse-time entities describing refined data types
  , DataDecl (..)
  , DataConP (..)
  , TyConP (..)

  -- * Pre-instantiated RType
  , RRType, BRType, RRProp
  , BSort, BPVar

  -- * Instantiated RType
  , BareType, PrType
  , SpecType, SpecProp
  , RSort
  , UsedPVar, RPVar, RReft
  , REnv (..)

  -- * Constructing & Destructing RTypes
  , RTypeRep(..), fromRTypeRep, toRTypeRep
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow
  , mkUnivs, bkUniv, bkClass
  , rFun, rCls, rRCls

  -- * Manipulating `Predicates`
  , pvars, pappSym, pApp

  -- * Some tests on RTypes
  , isBase
  , isFunTy
  , isTrivial

  -- * Traversing `RType`
  , efoldReft, foldReft
  , mapReft, mapReftM
  , mapBot, mapBind

  -- * ???
  , Oblig(..)
  , ignoreOblig
  , addTermCond
  , addInvCond


  -- * Inferred Annotations
  , AnnInfo (..)
  , Annot (..)

  -- * Overall Output
  , Output (..)

  -- * Refinement Hole
  , hole, isHole, hasHole

  -- * Converting To and From Sort
  , ofRSort, toRSort
  , rTypeValueVar
  , rTypeReft
  , stripRTypeBase

  -- * Class for values that can be pretty printed
  , PPrint (..)
  , showpp

  -- * Printer Configuration
  , PPEnv (..)
  , Tidy  (..)
  , ppEnv
  , ppEnvShort

  -- * Modules and Imports
  , ModName (..), ModType (..)
  , isSrcImport, isSpecImport
  , getModName, getModString

  -- * Refinement Type Aliases
  , RTEnv (..)
  , mapRT, mapRP, mapRE

  -- * Final Result
  , Result (..)

  -- * Errors and Error Messages
  , Error
  , TError (..)
  , EMsg (..)
  -- , LParseError (..)
  , ErrorResult
  , errSpan
  , errOther
  , errToFCrash

  -- * Source information (associated with constraints)
  , Cinfo (..)

  -- * Measures
  , Measure (..)
  , CMeasure (..)
  , Def (..)
  , Body (..)

  -- * Type Classes
  , RClass (..)

  -- * KV Profiling
  , KVKind (..)   -- types of kvars
  , KVProf        -- profile table
  , emptyKVProf   -- empty profile
  , updKVProf     -- extend profile

  -- * Misc
  , mapRTAVars
  , insertsSEnv

  -- * Strata
  , Stratum(..), Strata
  , isSVar
  , getStrata
  , makeDivType, makeFinType

  -- * CoreToLogic
  , LogicMap, toLogicMap, eAppWithMap, LMap(..)

  -- * Refined Instances
  , RDEnv, DEnv(..), RInstance(..)

  -- * Ureftable Instances
  , UReftable(..)

  )
  where

import SrcLoc                                   (noSrcSpan, SrcSpan)
import TyCon
import DataCon
import NameSet
import Module                                   (moduleNameFS)
import TypeRep                          hiding  (maybeParen, pprArrowChain)
import Var
import Text.Printf
import GHC                                      (HscEnv, ModuleName, moduleNameString)
import GHC.Generics
import Language.Haskell.Liquid.GhcMisc

import PrelInfo         (isNumericClass)


import TysWiredIn                               (listTyCon)
import Control.Arrow                            (second)
import Control.Monad                            (liftM, liftM2, liftM3, liftM4)
import qualified Control.Monad.Error as Ex
import Control.DeepSeq
import Control.Applicative                      ((<$>))
import Data.Typeable                            (Typeable)
import Data.Generics                            (Data)
import Data.Monoid                              hiding ((<>))
import qualified  Data.Foldable as F
import            Data.Hashable
import qualified  Data.HashMap.Strict as M
import qualified  Data.HashSet as S
import            Data.Maybe                   (fromMaybe)
import            Data.Traversable             hiding (mapM)
import            Data.List                    (nub)
import            Data.Text                    (Text)
import qualified  Data.Text                    as T
import Text.Parsec.Pos              (SourcePos)
import Text.Parsec.Error            (ParseError)
import Text.PrettyPrint.HughesPJ
import Language.Fixpoint.Config     hiding (Config)
import Language.Fixpoint.Misc
import Language.Fixpoint.Types      hiding (Result, Predicate, Def, R)
import Language.Fixpoint.Names      (funConName, listConName, tupConName)
import qualified Language.Fixpoint.PrettyPrint as F
import CoreSyn (CoreBind)

import Language.Haskell.Liquid.Variance
import Language.Haskell.Liquid.Misc (mapSndM, safeZip3WithError)


import Data.Default
-----------------------------------------------------------------------------
-- | Command Line Config Options --------------------------------------------
-----------------------------------------------------------------------------

-- NOTE: adding strictness annotations breaks the help message
data Config = Config {
    files          :: [FilePath] -- ^ source files to check
  , idirs          :: [FilePath] -- ^ path to directory for including specs
  , diffcheck      :: Bool       -- ^ check subset of binders modified (+ dependencies) since last check
  , real           :: Bool       -- ^ supports real number arithmetic
  , fullcheck      :: Bool       -- ^ check all binders (overrides diffcheck)
  , native         :: Bool       -- ^ use native (Haskell) fixpoint constraint solver
  , binders        :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , nowarnings     :: Bool       -- ^ disable warnings output (only show errors)
  , trustinternals :: Bool       -- ^ type all internal variables with true
  , nocaseexpand   :: Bool       -- ^ disable case expand
  , strata         :: Bool       -- ^ enable strata analysis
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , totality       :: Bool       -- ^ check totality in definitions
  , noPrune        :: Bool       -- ^ disable prunning unsorted Refinements
  , maxParams      :: Int        -- ^ the maximum number of parameters to accept when mining qualifiers
  , smtsolver      :: Maybe SMTSolver  -- ^ name of smtsolver to use [default: try z3, cvc4, mathsat in order]
  , shortNames     :: Bool       -- ^ drop module qualifers from pretty-printed names.
  , shortErrors    :: Bool       -- ^ don't show subtyping errors and contexts.
  , ghcOptions     :: [String]   -- ^ command-line options to pass to GHC
  , cFiles         :: [String]   -- ^ .c files to compile and link against (for GHC)
  } deriving (Data, Typeable, Show, Eq)


-----------------------------------------------------------------------------
-- | Printer ----------------------------------------------------------------
-----------------------------------------------------------------------------

data Tidy = Lossy | Full deriving (Eq, Ord)

class PPrint a where
  pprint     :: a -> Doc

  pprintTidy :: Tidy -> a -> Doc
  pprintTidy _ = pprint

showpp :: (PPrint a) => a -> String
showpp = render . pprint

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint

instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x, y)  = pprint x <+> text ":" <+> pprint y

data PPEnv
  = PP { ppPs    :: Bool
       , ppTyVar :: Bool -- TODO if set to True all Bare fails
       , ppSs    :: Bool
       , ppShort :: Bool
       }

ppEnv           = ppEnvPrintPreds
_ppEnvCurrent    = PP False False False False
ppEnvPrintPreds = PP False False False False
ppEnvShort pp   = pp { ppShort = True }



------------------------------------------------------------------
-- | GHC Information :  Code & Spec ------------------------------
------------------------------------------------------------------

data GhcInfo = GI {
    env      :: !HscEnv
  , cbs      :: ![CoreBind]
  , derVars  :: ![Var]
  , impVars  :: ![Var]
  , defVars  :: ![Var]
  , useVars  :: ![Var]
  , hqFiles  :: ![FilePath]
  , imports  :: ![String]
  , includes :: ![FilePath]
  , spec     :: !GhcSpec
  }

-- | The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries

data GhcSpec = SP {
    tySigs     :: ![(Var, Located SpecType)]     -- ^ Asserted Reftypes
                                                 -- eg.  see include/Prelude.spec
  , asmSigs    :: ![(Var, Located SpecType)]     -- ^ Assumed Reftypes
  , ctors      :: ![(Var, Located SpecType)]     -- ^ Data Constructor Measure Sigs
                                                 -- eg.  (:) :: a -> xs:[a] -> {v: Int | v = 1 + len(xs) }
  , meas       :: ![(Symbol, Located SpecType)]  -- ^ Measure Types
                                                 -- eg.  len :: [a] -> Int
  , invariants :: ![Located SpecType]            -- ^ Data Type Invariants
                                                 -- eg.  forall a. {v: [a] | len(v) >= 0}
  , ialiases   :: ![(Located SpecType, Located SpecType)] -- ^ Data Type Invariant Aliases
  , dconsP     :: ![(DataCon, DataConP)]         -- ^ Predicated Data-Constructors
                                                 -- e.g. see tests/pos/Map.hs
  , tconsP     :: ![(TyCon, TyConP)]             -- ^ Predicated Type-Constructors
                                                 -- eg.  see tests/pos/Map.hs
  , freeSyms   :: ![(Symbol, Var)]               -- ^ List of `Symbol` free in spec and corresponding GHC var
                                                 -- eg. (Cons, Cons#7uz) from tests/pos/ex1.hs
  , tcEmbeds   :: TCEmb TyCon                    -- ^ How to embed GHC Tycons into fixpoint sorts
                                                 -- e.g. "embed Set as Set_set" from include/Data/Set.spec
  , qualifiers :: ![Qualifier]                   -- ^ Qualifiers in Source/Spec files
                                                 -- e.g tests/pos/qualTest.hs
  , tgtVars    :: ![Var]                         -- ^ Top-level Binders To Verify (empty means ALL binders)
  , decr       :: ![(Var, [Int])]                -- ^ Lexicographically ordered size witnesses for termination
  , texprs     :: ![(Var, [Expr])]               -- ^ Lexicographically ordered expressions for termination
  , lvars      :: !(S.HashSet Var)               -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet Var)               -- ^ Binders to IGNORE during termination checking
  , config     :: !Config                        -- ^ Configuration Options
  , exports    :: !NameSet                       -- ^ `Name`s exported by the module being verified
  , measures   :: [Measure SpecType DataCon]
  , tyconEnv   :: M.HashMap TyCon RTyCon
  , dicts      :: DEnv Var SpecType              -- ^ Dictionary Environment
  }

type LogicMap = M.HashMap Symbol LMap

data LMap = LMap { lvar  :: Symbol
                 , largs :: [Symbol]
                 , lexpr :: Expr
                 }

instance Show LMap where
  show (LMap x xs e) = show x ++ " " ++ show xs ++ "\t|->\t" ++ show e


toLogicMap = M.fromList . map toLMap
  where
    toLMap (x, xs, e) = (x, LMap {lvar = x, largs = xs, lexpr = e})

eAppWithMap lmap f es def
  | Just (LMap _ xs e) <- M.lookup (val f) lmap
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = def


data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![PVar RSort]
                     , freeLabelTy  :: ![Symbol]
                     , varianceTs   :: !VarianceInfo
                     , variancePs   :: !VarianceInfo
                     , sizeFun      :: !(Maybe (Symbol -> Expr))
                     } deriving (Data, Typeable)

data DataConP = DataConP { dc_loc     :: !SourcePos
                         , freeTyVars :: ![RTyVar]
                         , freePred   :: ![PVar RSort]
                         , freeLabels :: ![Symbol]
                         , tyConsts   :: ![SpecType] -- ^ FIXME: WHAT IS THIS??
                         , tyArgs     :: ![(Symbol, SpecType)] -- ^ These are backwards, why??
                         , tyRes      :: !SpecType
                         , dc_locE    :: !SourcePos
                         } deriving (Data, Typeable)


-- | Which Top-Level Binders Should be Verified
data TargetVars = AllVars | Only ![Var]


--------------------------------------------------------------------
-- | Abstract Predicate Variables ----------------------------------
--------------------------------------------------------------------

data PVar t
  = PV { pname :: !Symbol
       , ptype :: !(PVKind t)
       , parg  :: !Symbol
       , pargs :: ![(t, Symbol, Expr)]
       }
    deriving (Generic, Data, Typeable, Show)

pvType p = case ptype p of
             PVProp t -> t
             PVHProp  -> errorstar "pvType on HProp-PVar"

data PVKind t
  = PVProp t | PVHProp
    deriving (Generic, Data, Typeable, F.Foldable, Traversable, Show)

instance Eq (PVar t) where
  pv == pv' = pname pv == pname pv' {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _ _)  (PV n' _ _ _) = compare n n'

instance Functor PVKind where
  fmap f (PVProp t) = PVProp (f t)
  fmap _ (PVHProp)  = PVHProp

instance Functor PVar where
  fmap f (PV x t v txys) = PV x (f <$> t) v (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVKind a) where
  rnf (PVProp t) = rnf t
  rnf (PVHProp)  = ()

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t v txys) = rnf n `seq` rnf v `seq` rnf t `seq` rnf txys

instance Hashable (PVar a) where
  hashWithSalt i (PV n _ _ _) = hashWithSalt i n



--------------------------------------------------------------------
------ Strictness --------------------------------------------------
--------------------------------------------------------------------

instance NFData Var
instance NFData SrcSpan
--------------------------------------------------------------------
------------------ Predicates --------------------------------------
--------------------------------------------------------------------

type UsedPVar      = PVar ()
newtype Predicate  = Pr [UsedPVar] deriving (Generic, Data, Typeable)

instance NFData Predicate where
  rnf _ = ()

instance Monoid Predicate where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Monoid a) => Monoid (UReft a) where
  mempty                         = U mempty mempty mempty
  mappend (U x y z) (U x' y' z') = U (mappend x x') (mappend y y') (mappend z z')


pdTrue         = Pr []
pdAnd ps       = Pr (nub $ concatMap pvars ps)
pvars (Pr pvs) = pvs

instance Subable UsedPVar where
  syms pv         = [ y | (_, x, EVar y) <- pargs pv, x /= y ]
  subst s pv      = pv { pargs = mapThd3 (subst s)  <$> pargs pv }
  substf f pv     = pv { pargs = mapThd3 (substf f) <$> pargs pv }
  substa f pv     = pv { pargs = mapThd3 (substa f) <$> pargs pv }


instance Subable Predicate where
  syms (Pr pvs)     = concatMap syms pvs
  subst s (Pr pvs)  = Pr (subst s <$> pvs)
  substf f (Pr pvs) = Pr (substf f <$> pvs)
  substa f (Pr pvs) = Pr (substa f <$> pvs)

instance Subable Qualifier where
  syms   = syms . q_body
  subst  = mapQualBody . subst
  substf = mapQualBody . substf
  substa = mapQualBody . substa

mapQualBody f q = q { q_body = f (q_body q) }

instance NFData r => NFData (UReft r) where
  rnf (U r p s) = rnf r `seq` rnf p `seq` rnf s

instance NFData Strata where
  rnf _ = ()

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()


-- MOVE TO TYPES
newtype RTyVar = RTV TyVar deriving (Generic, Data, Typeable)

instance Symbolic RTyVar where
  symbol (RTV tv) = symbol . T.pack . showPpr $ tv


data RTyCon = RTyCon
  { rtc_tc    :: TyCon         -- ^ GHC Type Constructor
  , rtc_pvars :: ![RPVar]      -- ^ Predicate Parameters
  , rtc_info  :: !TyConInfo    -- ^ TyConInfo
  }
  deriving (Generic, Data, Typeable)

-- | Accessors for @RTyCon@


isClassRTyCon = isClassTyCon . rtc_tc
rTyConPVs     = rtc_pvars
rTyConPropVs  = filter isPropPV . rtc_pvars
isPropPV      = isProp . ptype



isClassType (RApp c _ _ _) = isClass c
isClassType _              = False

-- rTyConPVHPs = filter isHPropPV . rtc_pvars
-- isHPropPV   = not . isPropPV

isProp (PVProp _) = True
isProp _          = False


defaultTyConInfo = TyConInfo [] [] Nothing

instance Default TyConInfo where
  def = defaultTyConInfo


-----------------------------------------------------------------------
-- | Co- and Contra-variance for TyCon --------------------------------
-----------------------------------------------------------------------

-- | Indexes start from 0 and type or predicate arguments can be both
--   covariant and contravaariant e.g., for the below Foo dataType
--
--     data Foo a b c d <p :: b -> Prop, q :: Int -> Prop, r :: a -> Prop>
--       = F (a<r> -> b<p>) | Q (c -> a) | G (Int<q> -> a<r>)
--
--  there will be:
--
--    varianceTyArgs     = [Bivariant , Covariant, Contravatiant, Invariant]
--    variancePsArgs     = [Covariant, Contravatiant, Bivariant]
--

data TyConInfo = TyConInfo
  { varianceTyArgs  :: !VarianceInfo             -- ^ variance info for type variables
  , variancePsArgs  :: !VarianceInfo             -- ^ variance info for predicate variables
  , sizeFunction    :: !(Maybe (Symbol -> Expr)) -- ^ logical function that computes the size of the structure
  } deriving (Generic, Data, Typeable)


instance Show TyConInfo where
  show (TyConInfo x y _) = show x ++ "\n" ++ show y

--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------

-- MOVE TO TYPES
data RType c tv r
  = RVar {
      rt_var    :: !tv
    , rt_reft   :: !r
    }

  | RFun  {
      rt_bind   :: !Symbol
    , rt_in     :: !(RType c tv r)
    , rt_out    :: !(RType c tv r)
    , rt_reft   :: !r
    }

  | RAllT {
      rt_tvbind :: !tv
    , rt_ty     :: !(RType c tv r)
    }

  | RAllP {
      rt_pvbind :: !(PVar (RType c tv ()))
    , rt_ty     :: !(RType c tv r)
    }

  | RAllS {
      rt_sbind  :: !(Symbol)
    , rt_ty     :: !(RType c tv r)
    }

  | RApp  {
      rt_tycon  :: !c
    , rt_args   :: ![RType  c tv r]
    , rt_pargs  :: ![RTProp c tv r]
    , rt_reft   :: !r
    }

  | RAllE {
      rt_bind   :: !Symbol
    , rt_allarg :: !(RType c tv r)
    , rt_ty     :: !(RType c tv r)
    }

  | REx {
      rt_bind   :: !Symbol
    , rt_exarg  :: !(RType c tv r)
    , rt_ty     :: !(RType c tv r)
    }

  | RExprArg (Located Expr)                     -- ^ For expression arguments to type aliases
                                                --   see tests/pos/vector2.hs
  | RAppTy{
      rt_arg   :: !(RType c tv r)
    , rt_res   :: !(RType c tv r)
    , rt_reft  :: !r
    }

  | RRTy  {
      rt_env   :: ![(Symbol, RType c tv r)]
    , rt_ref   :: !r
    , rt_obl   :: !Oblig
    , rt_ty    :: !(RType c tv r)
    }

  | RHole r -- ^ let LH match against the Haskell type and add k-vars, e.g. `x:_`
            --   see tests/pos/Holes.hs
  deriving (Generic, Data, Typeable)

data Oblig
  = OTerm -- ^ Obligation that proves termination
  | OInv  -- ^ Obligation that proves invariants
  | OCons -- ^ Obligation that proves constraints
  deriving (Generic, Data, Typeable)

ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t

instance Show Oblig where
  show OTerm = "termination-condition"
  show OInv  = "invariant-obligation"
  show OCons = "constraint-obligation"

instance PPrint Oblig where
  pprint = text . show

-- | @Ref@ describes `Prop τ` and `HProp` arguments applied to type constructors.
--   For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
--   * the `RProp`  denoted by `{\h -> v > h}` to
--   * the `RTyCon` denoted by `[]`.
--   Thus, @Ref@ is used for abstract-predicate (arguments) that are associated
--   with _type constructors_ i.e. whose semantics are _dependent upon_ the data-type.
--   In contrast, the `Predicate` argument in `ur_pred` in the @UReft@ applies
--   directly to any type and has semantics _independent of_ the data-type.

data Ref τ r t
  = RPropP {
      rf_args :: [(Symbol, τ)]
    , rf_reft :: r
    }                              -- ^ Parse-time `RProp`

  | RProp  {
      rf_args :: [(Symbol, τ)]
    , rf_body :: t
    }                              -- ^ Abstract refinement associated with `RTyCon`

  | RHProp {
      rf_args :: [(Symbol, τ)]
    , rf_heap :: World t
    }                              -- ^ Abstract heap-refinement associated with `RTyCon`
  deriving (Generic, Data, Typeable)

-- | @RTProp@ is a convenient alias for @Ref@ that will save a bunch of typing.
--   In general, perhaps we need not expose @Ref@ directly at all.
type RTProp c tv r = Ref (RType c tv ()) r (RType c tv r)


-- | A @World@ is a Separation Logic predicate that is essentially a sequence of binders
--   that satisfies two invariants (TODO:LIQUID):
--   1. Each `hs_addr :: Symbol` appears at most once,
--   2. There is at most one `HVar` in a list.

newtype World t = World [HSeg t]
                deriving (Generic, Data, Typeable)

data    HSeg  t = HBind {hs_addr :: !Symbol, hs_val :: t}
                | HVar UsedPVar
                deriving (Generic, Data, Typeable)

data UReft r
  = U { ur_reft :: !r, ur_pred :: !Predicate, ur_strata :: !Strata }
    deriving (Generic, Data, Typeable)

type BRType     = RType LocSymbol Symbol
type RRType     = RType RTyCon    RTyVar

type BSort      = BRType    ()
type RSort      = RRType    ()

type BPVar      = PVar      BSort
type RPVar      = PVar      RSort

type RReft      = UReft     Reft
type PrType     = RRType    Predicate
type BareType   = BRType    RReft
type SpecType   = RRType    RReft
type SpecProp   = RRProp    RReft
type RRProp r   = Ref       RSort r (RRType r)


data Stratum    = SVar Symbol | SDiv | SWhnf | SFin
                  deriving (Generic, Data, Typeable, Eq)

type Strata = [Stratum]

isSVar (SVar _) = True
isSVar _        = False

instance Monoid Strata where
  mempty        = []
  mappend s1 s2 = nub $ s1 ++ s2

class SubsTy tv ty a where
  subt :: (tv, ty) -> a -> a

class (Eq c) => TyConable c where
  isFun    :: c -> Bool
  isList   :: c -> Bool
  isTuple  :: c -> Bool
  ppTycon  :: c -> Doc
  isClass  :: c -> Bool

  isNumCls  :: c -> Bool
  isFracCls :: c -> Bool

  isClass   = const False
  isNumCls  = const False
  isFracCls = const False

class ( TyConable c
      , Eq c, Eq tv
      , Hashable tv
      , Reftable r
      , PPrint r
      ) => RefTypable c tv r
  where
--     ppCls    :: p -> [RType c tv r] -> Doc
    ppRType  :: Prec -> RType c tv r -> Doc



-------------------------------------------------------------------------------
-- | TyConable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

-- MOVE TO TYPES
instance TyConable RTyCon where
  isFun      = isFunTyCon . rtc_tc
  isList     = (listTyCon ==) . rtc_tc
  isTuple    = TyCon.isTupleTyCon   . rtc_tc
  isClass    = isClassRTyCon
  ppTycon    = toFix

  isNumCls c  = maybe False isNumericClass    (tyConClass_maybe $ rtc_tc c)
  isFracCls c = maybe False isFractionalClass (tyConClass_maybe $ rtc_tc c)

-- MOVE TO TYPES
instance TyConable Symbol where
  isFun   s = funConName == s
  isList  s = listConName == s
  isTuple s = tupConName == s
  ppTycon = text . symbolString

instance TyConable LocSymbol where
  isFun   = isFun . val
  isList  = isList . val
  isTuple = isTuple . val
  ppTycon = ppTycon . val


instance Eq RTyCon where
  x == y = rtc_tc x == rtc_tc y

instance Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c -- <+> text "\n<<" <+> hsep (map toFix ts) <+> text ">>\n"


instance PPrint RTyCon where
  pprint = text . showPpr . rtc_tc


instance Show RTyCon where
  show = showpp

--------------------------------------------------------------------------
-- | Refined Instances ---------------------------------------------------
--------------------------------------------------------------------------

data RInstance t = RI { riclass :: LocSymbol
                      , ritype  :: t
                      , risigs  :: [(LocSymbol, t)]
                      }

newtype DEnv x ty = DEnv (M.HashMap x (M.HashMap Symbol ty)) deriving (Monoid)

type RDEnv = DEnv Var SpecType

instance Functor RInstance where
  fmap f (RI x t xts) = RI x (f t) (mapSnd f <$> xts)


--------------------------------------------------------------------------
-- | Values Related to Specifications ------------------------------------
--------------------------------------------------------------------------


-- | Data type refinements
data DataDecl   = D { tycName   :: LocSymbol
                                -- ^ Type  Constructor Name
                    , tycTyVars :: [Symbol]
                                -- ^ Tyvar Parameters
                    , tycPVars  :: [PVar BSort]
                                -- ^ PVar  Parameters
                    , tycTyLabs :: [Symbol]
                                -- ^ PLabel  Parameters
                    , tycDCons  :: [(LocSymbol, [(Symbol, BareType)])]
                                -- ^ [DataCon, [(fieldName, fieldType)]]
                    , tycSrcPos :: !SourcePos
                                -- ^ Source Position
                    , tycSFun   :: (Maybe (Symbol -> Expr))
                                -- ^ Measure that should decrease in recursive calls
                    }
     --              deriving (Show)


instance Eq DataDecl where
   d1 == d2 = (tycName d1) == (tycName d2)

instance Ord DataDecl where
   compare d1 d2 = compare (tycName d1) (tycName d2)

-- | For debugging.
instance Show DataDecl where
  show dd = printf "DataDecl: data = %s, tyvars = %s"
              (show $ tycName   dd)
              (show $ tycTyVars dd)

-- | Refinement Type Aliases

data RTAlias tv ty
  = RTA { rtName  :: Symbol
        , rtTArgs :: [tv]
        , rtVArgs :: [tv]
        , rtBody  :: ty
        , rtPos   :: SourcePos
        , rtPosE  :: SourcePos
        }

mapRTAVars f rt = rt { rtTArgs = f <$> rtTArgs rt
                     , rtVArgs = f <$> rtVArgs rt
                     }

------------------------------------------------------------------------
-- | Constructor and Destructors for RTypes ----------------------------
------------------------------------------------------------------------

data RTypeRep c tv r
  = RTypeRep { ty_vars   :: [tv]
             , ty_preds  :: [PVar (RType c tv ())]
             , ty_labels :: [Symbol]
             , ty_binds  :: [Symbol]
             , ty_refts  :: [r]
             , ty_args   :: [RType c tv r]
             , ty_res    :: (RType c tv r)
             }

fromRTypeRep (RTypeRep {..})
  = mkArrow ty_vars ty_preds ty_labels arrs ty_res
  where
    arrs = safeZip3WithError "fromRTypeRep" ty_binds ty_args ty_refts

toRTypeRep           :: RType c tv r -> RTypeRep c tv r
toRTypeRep t         = RTypeRep αs πs ls xs rs ts t''
  where
    (αs, πs, ls, t')  = bkUniv  t
    (xs, ts, rs, t'') = bkArrow t'

mkArrow αs πs ls xts = mkUnivs αs πs ls . mkArrs xts
  where
    mkArrs xts t  = foldr (\(b,t1,r) t2 -> RFun b t1 t2 r) t xts

bkArrowDeep (RAllT _ t)     = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RAllS _ t)     = bkArrowDeep t
bkArrowDeep (RFun x t t' r) = let (xs, ts, rs, t'') = bkArrowDeep t'  in (x:xs, t:ts, r:rs, t'')
bkArrowDeep t               = ([], [], [], t)

bkArrow (RFun x t t' r) = let (xs, ts, rs, t'') = bkArrow t'  in (x:xs, t:ts, r:rs, t'')
bkArrow t               = ([], [], [], t)

safeBkArrow (RAllT _ _) = errorstar "safeBkArrow on RAllT"
safeBkArrow (RAllP _ _) = errorstar "safeBkArrow on RAllP"
safeBkArrow (RAllS _ t) = safeBkArrow t
safeBkArrow t           = bkArrow t

mkUnivs αs πs ls t = foldr RAllT (foldr RAllP (foldr RAllS t ls) πs) αs

bkUniv :: RType t1 a t2 -> ([a], [PVar (RType t1 a ())], [Symbol], RType t1 a t2)
bkUniv (RAllT α t)      = let (αs, πs, ls, t') = bkUniv t in  (α:αs, πs, ls, t')
bkUniv (RAllP π t)      = let (αs, πs, ls, t') = bkUniv t in  (αs, π:πs, ls, t')
bkUniv (RAllS s t)      = let (αs, πs, ss, t') = bkUniv t in  (αs, πs, s:ss, t')
bkUniv t                = ([], [], [], t)

bkClass (RFun _ (RApp c t _ _) t' _)
  | isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RRTy e r o t)
  = let (cs, t') = bkClass t in (cs, RRTy e r o t')
bkClass t
  = ([], t)

rFun b t t' = RFun b t t' mempty
rCls c ts   = RApp (RTyCon c [] defaultTyConInfo) ts [] mempty
rRCls rc ts = RApp rc ts [] mempty

addTermCond = addObligation OTerm

addInvCond :: SpecType -> RReft -> SpecType
addInvCond t r'
  | isTauto $ ur_reft r' -- null rv
  = t
  | otherwise
  = fromRTypeRep $ trep {ty_res = RRTy [(x', tbd)] r OInv tbd}
  where
    trep = toRTypeRep t
    tbd  = ty_res trep
    r    = r' {ur_reft = Reft (v, Refa rx)}
    su   = (v, EVar x')
    x'   = "xInv"
    rx   = PIff (PBexp $ EVar v) $ subst1 (raPred rv) su
    Reft(v, rv) = ur_reft r'

addObligation :: Oblig -> SpecType -> RReft -> SpecType
addObligation o t r  = mkArrow αs πs ls xts $ RRTy [] r o t2
  where
    (αs, πs, ls, t1) = bkUniv t
    (xs, ts, rs, t2) = bkArrow t1
    xts              = zip3 xs ts rs

--------------------------------------------

instance Subable Stratum where
  syms (SVar s) = [s]
  syms _        = []
  subst su (SVar s) = SVar $ subst su s
  subst _ s         = s
  substf f (SVar s) = SVar $ substf f s
  substf _ s        = s
  substa f (SVar s) = SVar $ substa f s
  substa _ s        = s

instance Subable Strata where
  syms s     = concatMap syms s
  subst su   = (subst su <$>)
  substf f   = (substf f <$>)
  substa f   = (substa f <$>)

instance Reftable Strata where
  isTauto []         = True
  isTauto _          = False

  ppTy _             = error "ppTy on Strata"
  toReft _           = mempty
  params s           = [l | SVar l <- s]
  bot _              = []
  top _              = []

  ofReft = error "TODO: Strata.ofReft"


class Reftable r => UReftable r where
  ofUReft :: UReft Reft -> r
  ofUReft (U r _ _) = ofReft r


instance UReftable (UReft Reft) where
   ofUReft r = r

instance UReftable () where
   ofUReft _ = mempty

instance (PPrint r, Reftable r) => Reftable (UReft r) where
  isTauto            = isTauto_ureft
  ppTy               = ppTy_ureft
  toReft (U r ps _)  = toReft r `meet` toReft ps
  params (U r _ _)   = params r
  bot (U r _ s)      = U (bot r) (Pr []) (bot s)
  top (U r p s)      = U (top r) (top p) (top s)

  ofReft r = U (ofReft r) mempty mempty

isTauto_ureft u      = isTauto (ur_reft u) && isTauto (ur_pred u) -- && (isTauto $ ur_strata u)

ppTy_ureft u@(U r p s) d
  | isTauto_ureft  u  = d
  | otherwise         = ppr_reft r (ppTy p d) s

ppr_reft r d s       = braces (pprint v <+> colon <+> d <> ppr_str s <+> text "|" <+> pprint r')
  where
    r'@(Reft (v, _)) = toReft r

ppr_str [] = empty
ppr_str s  = text "^" <> pprint s

instance Subable r => Subable (UReft r) where
  syms (U r p _)     = syms r ++ syms p
  subst s (U r z l)  = U (subst s r) (subst s z) (subst s l)
  substf f (U r z l) = U (substf f r) (substf f z) (substf f l)
  substa f (U r z l) = U (substa f r) (substa f z) (substa f l)

instance (Reftable r, RefTypable c tv r) => Subable (RTProp c tv r) where
  syms (RPropP ss r)     = (fst <$> ss) ++ syms r
  syms (RProp  ss r)     = (fst <$> ss) ++ syms r
  syms (RHProp _  _)     = error "TODO: PHProp.syms"

  subst su (RPropP ss r) = RPropP ss (subst su r)
  subst su (RProp  ss t) = RProp ss (subst su <$> t)
  subst _  (RHProp _  _) = error "TODO: PHProp.subst"

  substf f (RPropP ss r) = RPropP ss (substf f r)
  substf f (RProp  ss t) = RProp ss (substf f <$> t)
  substf _ (RHProp _  _) = error "TODO PHProp.substf"
  substa f (RPropP ss r) = RPropP ss (substa f r)
  substa f (RProp  ss t) = RProp ss (substa f <$> t)
  substa _ (RHProp _  _) = error "TODO PHProp.substa"

instance (Subable r, RefTypable c tv r) => Subable (RType c tv r) where
  syms        = foldReft (\r acc -> syms r ++ acc) []
  substa f    = mapReft (substa f)
  substf f    = emapReft (substf . substfExcept f) []
  subst su    = emapReft (subst  . substExcept su) []
  subst1 t su = emapReft (\xs r -> subst1Except xs r su) [] t




instance Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = errorstar "No BOT instance for Predicate"
  -- NV: This does not print abstract refinements....
  -- HACK: Hiding to not render types in WEB DEMO. NEED TO FIX.
  ppTy r d | isTauto r        = d
           | not (ppPs ppEnv) = d
           | otherwise        = d <> (angleBrackets $ pprint r)

  toReft (Pr ps@(p:_))        = Reft (parg p, refa $ pToRef <$> ps)
  toReft _                    = mempty
  params                      = errorstar "TODO: instance of params for Predicate"

  ofReft = error "TODO: Predicate.ofReft"

pToRef p = pApp (pname p) $ (EVar $ parg p) : (thd3 <$> pargs p)

pApp      :: Symbol -> [Expr] -> Pred
pApp p es = PBexp $ EApp (dummyLoc $ pappSym $ length es) (EVar p:es)

pappSym n  = symbol $ "papp" ++ show n

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

isTrivial t = foldReft (\r b -> isTauto r && b) True t

instance Functor UReft where
  fmap f (U r p s) = U (f r) p s

instance Functor (RType a b) where
  fmap  = mapReft

-- instance Fold.Foldable (RType a b c) where
--   foldr = foldReft

mapReft ::  (r1 -> r2) -> RType c tv r1 -> RType c tv r2
mapReft f = emapReft (\_ -> f) []

emapReft ::  ([Symbol] -> r1 -> r2) -> [Symbol] -> RType c tv r1 -> RType c tv r2

emapReft f γ (RVar α r)          = RVar  α (f γ r)
emapReft f γ (RAllT α t)         = RAllT α (emapReft f γ t)
emapReft f γ (RAllP π t)         = RAllP π (emapReft f γ t)
emapReft f γ (RAllS p t)         = RAllS p (emapReft f γ t)
emapReft f γ (RFun x t t' r)     = RFun  x (emapReft f γ t) (emapReft f (x:γ) t') (f γ r)
emapReft f γ (RApp c ts rs r)    = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (RAllE z t t')      = RAllE z (emapReft f γ t) (emapReft f γ t')
emapReft f γ (REx z t t')        = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)        = RExprArg e
emapReft f γ (RAppTy t t' r)     = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft f γ (RRTy e r o t)      = RRTy  (mapSnd (emapReft f γ) <$> e) (f γ r) o (emapReft f γ t)
emapReft f γ (RHole r)           = RHole (f γ r)

emapRef :: ([Symbol] -> t -> s) ->  [Symbol] -> RTProp c tv t -> RTProp c tv s
emapRef  f γ (RPropP s r)         = RPropP s $ f γ r
emapRef  f γ (RProp  s t)         = RProp s $ emapReft f γ t
emapRef  _ _ (RHProp _ _)         = error "TODO: PHProp empaReft"

------------------------------------------------------------------------------------------------------
-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t

-- isBase :: RType a -> Bool
isBase (RAllT _ t)      = isBase t
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RFun _ t1 t2 _) = isBase t1 && isBase t2
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase (RRTy _ _ _ t)   = isBase t
isBase (RAllE _ _ t)    = isBase t
isBase _                = False

isFunTy (RAllE _ _ t)    = isFunTy t
isFunTy (RAllS _ t)      = isFunTy t
isFunTy (RAllT _ t)      = isFunTy t
isFunTy (RAllP _ t)      = isFunTy t
isFunTy (RFun _ _ _ _)   = True
isFunTy _                = False


mapReftM :: (Monad m) => (r1 -> m r2) -> RType c tv r1 -> m (RType c tv r2)
mapReftM f (RVar α r)         = liftM   (RVar  α)   (f r)
mapReftM f (RAllT α t)        = liftM   (RAllT α)   (mapReftM f t)
mapReftM f (RAllP π t)        = liftM   (RAllP π)   (mapReftM f t)
mapReftM f (RAllS s t)        = liftM   (RAllS s)   (mapReftM f t)
mapReftM f (RFun x t t' r)    = liftM3  (RFun x)    (mapReftM f t)          (mapReftM f t')       (f r)
mapReftM f (RApp c ts rs r)   = liftM3  (RApp  c)   (mapM (mapReftM f) ts)  (mapM (mapRefM f) rs) (f r)
mapReftM f (RAllE z t t')     = liftM2  (RAllE z)   (mapReftM f t)          (mapReftM f t')
mapReftM f (REx z t t')       = liftM2  (REx z)     (mapReftM f t)          (mapReftM f t')
mapReftM _ (RExprArg e)       = return  $ RExprArg e
mapReftM f (RAppTy t t' r)    = liftM3  RAppTy (mapReftM f t) (mapReftM f t') (f r)
mapReftM f (RHole r)          = liftM   RHole       (f r)
mapReftM f (RRTy xts r o t)   = liftM4  RRTy (mapM (mapSndM (mapReftM f)) xts) (f r) (return o) (mapReftM f t)

mapRefM  :: (Monad m) => (t -> m s) -> (RTProp c tv t) -> m (RTProp c tv s)
mapRefM  f (RPropP s r)       = liftM   (RPropP s)     (f r)
mapRefM  f (RProp  s t)       = liftM   (RProp s)      (mapReftM f t)
mapRefM  _ (RHProp _ _)       = error "TODO PHProp.mapRefM"

-- foldReft :: (r -> a -> a) -> a -> RType c tv r -> a
foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) (\_ γ -> γ) emptySEnv

-- efoldReft :: Reftable r =>(p -> [RType c tv r] -> [(Symbol, a)])-> (RType c tv r -> a)-> (SEnv a -> Maybe (RType c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType c tv r-> c1
efoldReft cb g f fp = go
  where
    -- folding over RType
    go γ z me@(RVar _ r)                = f γ (Just me) r z
    go γ z (RAllT _ t)                  = go γ z t
    go γ z (RAllP p t)                  = go (fp p γ) z t
    go γ z (RAllS _ t)                  = go γ z t
    go γ z me@(RFun _ (RApp c ts _ _) t' r)
       | isClass c                      = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t')
    go γ z me@(RFun x t t' r)           = f γ (Just me) r (go (insertSEnv x (g t) γ) (go γ z t) t')
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' (insertSEnv (rTypeValueVar me) (g me) γ) z ts) rs)

    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z me@(RRTy [] r _ t)          = f γ (Just me) r (go γ z t)
    go γ z me@(RRTy xts r _ t)          = f γ (Just me) r (go γ (go γ z (envtoType xts)) t)
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z
    go γ z me@(RHole r)                 = f γ (Just me) r z

    -- folding over Ref
    ho  γ z (RPropP ss r)               = f (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) Nothing r z
    ho  γ z (RProp  ss t)               = go (insertsSEnv γ ((mapSnd (g . ofRSort)) <$> ss)) z t
    ho  _ _ (RHProp _  _)               = error "TODO: RHProp.ho"

    -- folding over [RType]
    go' γ z ts                 = foldr (flip $ go γ) z ts

    -- folding over [Ref]
    ho' γ z rs                 = foldr (flip $ ho γ) z rs

    envtoType xts = foldr (\(x,t1) t2 -> rFun x t1 t2) (snd $ last xts) (init xts)

mapBot f (RAllT α t)       = RAllT α (mapBot f t)
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RAllS s t)       = RAllS s (mapBot f t)
mapBot f (RFun x t t' r)   = RFun x (mapBot f t) (mapBot f t') r
mapBot f (RAppTy t t' r)   = RAppTy (mapBot f t) (mapBot f t') r
mapBot f (RApp c ts rs r)  = f $ RApp c (mapBot f <$> ts) (mapBotRef f <$> rs) r
mapBot f (REx b t1 t2)     = REx b  (mapBot f t1) (mapBot f t2)
mapBot f (RAllE b t1 t2)   = RAllE b  (mapBot f t1) (mapBot f t2)
mapBot f (RRTy e r o t)    = RRTy (mapSnd (mapBot f) <$> e) r o (mapBot f t)
mapBot f t'                = f t'
mapBotRef _ (RPropP s r)    = RPropP s $ r
mapBotRef f (RProp  s t)    = RProp  s $ mapBot f t
mapBotRef _ (RHProp _ _)    = error "TODO: RHProp.mapBotRef"

mapBind f (RAllT α t)      = RAllT α (mapBind f t)
mapBind f (RAllP π t)      = RAllP π (mapBind f t)
mapBind f (RAllS s t)      = RAllS s (mapBind f t)
mapBind f (RFun b t1 t2 r) = RFun (f b)  (mapBind f t1) (mapBind f t2) r
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RAllE b t1 t2)  = RAllE  (f b) (mapBind f t1) (mapBind f t2)
mapBind f (REx b t1 t2)    = REx    (f b) (mapBind f t1) (mapBind f t2)
mapBind _ (RVar α r)       = RVar α r
mapBind _ (RHole r)        = RHole r
mapBind f (RRTy e r o t)   = RRTy e r o (mapBind f t)
mapBind _ (RExprArg e)     = RExprArg e
mapBind f (RAppTy t t' r)  = RAppTy (mapBind f t) (mapBind f t') r

mapBindRef f (RPropP s r)   = RPropP (mapFst f <$> s) r
mapBindRef f (RProp  s t)   = RProp  (mapFst f <$> s) $ mapBind f t
mapBindRef _ (RHProp _ _)   = error "TODO: RHProp.mapBindRef"


--------------------------------------------------
ofRSort ::  Reftable r => RType c tv () -> RType c tv r
ofRSort = fmap mempty

toRSort :: RType c tv r -> RType c tv ()
toRSort = stripAnnotations . mapBind (const dummySymbol) . fmap (const ())

stripAnnotations (RAllT α t)      = RAllT α (stripAnnotations t)
stripAnnotations (RAllP _ t)      = stripAnnotations t
stripAnnotations (RAllS _ t)      = stripAnnotations t
stripAnnotations (RAllE _ _ t)    = stripAnnotations t
stripAnnotations (REx _ _ t)      = stripAnnotations t
stripAnnotations (RFun x t t' r)  = RFun x (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RAppTy t t' r)  = RAppTy (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RApp c ts rs r) = RApp c (stripAnnotations <$> ts) (stripAnnotationsRef <$> rs) r
stripAnnotations (RRTy _ _ _ t)   = stripAnnotations t
stripAnnotations t                = t
stripAnnotationsRef (RProp s t)   = RProp s $ stripAnnotations t
stripAnnotationsRef r             = r


insertsSEnv  = foldr (\(x, t) γ -> insertSEnv x t γ)

rTypeValueVar :: (Reftable r) => RType c tv r -> Symbol
rTypeValueVar t = vv where Reft (vv,_) =  rTypeReft t

rTypeReft :: (Reftable r) => RType c tv r -> Reft
rTypeReft = fromMaybe trueReft . fmap toReft . stripRTypeBase

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase (RApp _ _ _ x)
  = Just x
stripRTypeBase (RVar _ x)
  = Just x
stripRTypeBase (RFun _ _ _ x)
  = Just x
stripRTypeBase (RAppTy _ _ x)
  = Just x
stripRTypeBase _
  = Nothing

mapRBase f (RApp c ts rs r) = RApp c ts rs $ f r
mapRBase f (RVar a r)       = RVar a $ f r
mapRBase f (RFun x t1 t2 r) = RFun x t1 t2 $ f r
mapRBase f (RAppTy t1 t2 r) = RAppTy t1 t2 $ f r
mapRBase _ t                = t



makeLType :: Stratum -> SpecType -> SpecType
makeLType l t = fromRTypeRep trep{ty_res = mapRBase f $ ty_res trep}
  where trep = toRTypeRep t
        f (U r p _) = U r p [l]


makeDivType = makeLType SDiv
makeFinType = makeLType SFin

getStrata = maybe [] ur_strata . stripRTypeBase

-----------------------------------------------------------------------------
-- | PPrint -----------------------------------------------------------------
-----------------------------------------------------------------------------

instance Show Stratum where
  show SFin = "Fin"
  show SDiv = "Div"
  show SWhnf = "Whnf"
  show (SVar s) = show s

instance PPrint Stratum where
  pprint = text . show

instance PPrint Strata where
  pprint [] = empty
  pprint ss = hsep (pprint <$> nub ss)

instance PPrint SourcePos where
  pprint = text . show

instance PPrint () where
  pprint = text . show

instance PPrint String where
  pprint = text

instance PPrint Text where
  pprint = text . T.unpack

instance PPrint a => PPrint (Located a) where
  pprint = pprint . val

instance PPrint Int where
  pprint = F.pprint

instance PPrint Integer where
  pprint = F.pprint

instance PPrint Constant where
  pprint = F.pprint

instance PPrint Brel where
  pprint = F.pprint

instance PPrint Bop where
  pprint = F.pprint

instance PPrint Sort where
  pprint = F.pprint

instance PPrint Symbol where
  pprint = pprint . symbolText

instance PPrint Expr where
  pprint = F.pprint

instance PPrint SymConst where
  pprint = F.pprint

instance PPrint Pred where
  pprint = F.pprint

instance PPrint a => PPrint (PVar a) where
  pprint (PV s _ _ xts)   = pprint s <+> hsep (pprint <$> dargs xts)
    where
      dargs               = map thd3 . takeWhile (\(_, x, y) -> EVar x /= y)

instance PPrint Predicate where
  pprint (Pr [])       = text "True"
  pprint (Pr pvs)      = hsep $ punctuate (text "&") (map pprint pvs)

instance PPrint Refa where
  pprint = pprint . raPred

instance PPrint Reft where
  pprint = F.pprint

instance PPrint SortedReft where
  pprint = F.pprint

------------------------------------------------------------------------
-- | Error Data Type ---------------------------------------------------
------------------------------------------------------------------------
-- | The type used during constraint generation, used also to define contexts
-- for errors, hence in this file, and NOT in Constraint.hs
newtype REnv = REnv  (M.HashMap Symbol SpecType)

type ErrorResult = FixResult Error

newtype EMsg     = EMsg String deriving (Generic, Data, Typeable)

instance PPrint EMsg where
  pprint (EMsg s) = text s

-- | In the below, we use EMsg instead of, say, SpecType because
--   the latter is impossible to serialize, as it contains GHC
--   internals like TyCon and Class inside it.

type Error = TError SpecType


-- | INVARIANT : all Error constructors should have a pos field
data TError t =
    ErrSubType { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error
  | ErrFCrash  { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error
  | ErrAssType { pos :: !SrcSpan
               , obl :: !Oblig
               , msg :: !Doc
               , ref :: !RReft
               } -- ^ liquid type error

  | ErrParse    { pos :: !SrcSpan
                , msg :: !Doc
                , err :: !ParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: !SrcSpan
                , var :: !Doc
                , typ :: !t
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrTermSpec { pos :: !SrcSpan
                , var :: !Doc
                , exp :: !Expr
                , msg :: !Doc
                } -- ^ sort error in specification
  | ErrDupAlias { pos  :: !SrcSpan
                , var  :: !Doc
                , kind :: !Doc
                , locs :: ![SrcSpan]
                } -- ^ multiple alias with same name error

  | ErrDupSpecs { pos :: !SrcSpan
                , var :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple specs for same binder error

  | ErrBadData  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ multiple specs for same binder error

  | ErrInvt     { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: !SrcSpan
                , t1  :: !t
                , t2  :: !t
                , msg :: !Doc
                } -- ^ Incompatible using error

  | ErrMeas     { pos :: !SrcSpan
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Measure sort error

  | ErrHMeas    { pos :: !SrcSpan
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Haskell bad Measure error

  | ErrUnbound  { pos :: !SrcSpan
                , var :: !Doc
                } -- ^ Unbound symbol in specification

  | ErrGhc      { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking

  | ErrMismatch { pos  :: !SrcSpan
                , var  :: !Doc
                , hs   :: !Type
                , lq   :: !Type
                } -- ^ Mismatch between Liquid and Haskell types

  | ErrAliasCycle { pos    :: !SrcSpan
                  , acycle :: ![(SrcSpan, Doc)]
                  } -- ^ Cyclic Refined Type Alias Definitions

  | ErrIllegalAliasApp { pos   :: !SrcSpan
                       , dname :: !Doc
                       , dpos  :: !SrcSpan
                       } -- ^ Illegal RTAlias application (from BSort, eg. in PVar)

  | ErrAliasApp { pos   :: !SrcSpan
                , nargs :: !Int
                , dname :: !Doc
                , dpos  :: !SrcSpan
                , dargs :: !Int
                }

  | ErrSaved    { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrTermin   { bind :: ![Var]
                , pos  :: !SrcSpan
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrRClass   { pos   :: !SrcSpan
                , cls   :: !Doc
                , insts :: ![(SrcSpan, Doc)]
                } -- ^ Refined Class/Interfaces Conflict

  | ErrOther    { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ Unexpected PANIC
  deriving (Typeable, Functor)

-- data LParseError = LPE !SourcePos [String]
--                    deriving (Data, Typeable, Generic)




errToFCrash :: Error -> Error
errToFCrash (ErrSubType l m g t1 t2)
  = ErrFCrash l m g t1 t2
errToFCrash e
  = e


instance Eq Error where
  e1 == e2 = pos e1 == pos e2

instance Ord Error where
  e1 <= e2 = pos e1 <= pos e2

instance Ex.Error Error where
  strMsg = errOther . pprint

errSpan :: TError a -> SrcSpan
errSpan = pos

errOther :: Doc -> Error
errOther = ErrOther noSrcSpan

------------------------------------------------------------------------
-- | Source Information Associated With Constraints --------------------
------------------------------------------------------------------------

data Cinfo    = Ci { ci_loc :: !SrcSpan
                   , ci_err :: !(Maybe Error)
                   }
                deriving (Eq, Ord)

instance NFData Cinfo


------------------------------------------------------------------------
-- | Converting Results To Answers -------------------------------------
------------------------------------------------------------------------

class Result a where
  result :: a -> FixResult Error

instance Result [Error] where
  result es = Crash es ""

instance Result Error where
  result (ErrOther _ d) = UnknownError $ render d
  result e              = result [e]

instance Result (FixResult Cinfo) where
  result = fmap cinfoError

--------------------------------------------------------------------------------
--- Module Names
--------------------------------------------------------------------------------

data ModName = ModName !ModType !ModuleName deriving (Eq,Ord)

instance Show ModName where
  show = getModString

instance Symbolic ModName where
  symbol (ModName _ m) = symbol m

instance Symbolic ModuleName where
  symbol = symbol . moduleNameFS

data ModType = Target | SrcImport | SpecImport deriving (Eq,Ord)

isSrcImport (ModName SrcImport _) = True
isSrcImport _                     = False

isSpecImport (ModName SpecImport _) = True
isSpecImport _                      = False

getModName (ModName _ m) = m

getModString = moduleNameString . getModName


-------------------------------------------------------------------------------
----------- Refinement Type Aliases -------------------------------------------
-------------------------------------------------------------------------------

data RTEnv   = RTE { typeAliases :: M.HashMap Symbol (RTAlias RTyVar SpecType)
                   , predAliases :: M.HashMap Symbol (RTAlias Symbol Pred)
                   , exprAliases :: M.HashMap Symbol (RTAlias Symbol Expr)
                   }

instance Monoid RTEnv where
  (RTE ta1 pa1 ea1) `mappend` (RTE ta2 pa2 ea2)
    = RTE (ta1 `M.union` ta2) (pa1 `M.union` pa2) (ea1 `M.union` ea2)
  mempty = RTE M.empty M.empty M.empty

mapRT f e = e { typeAliases = f $ typeAliases e }
mapRP f e = e { predAliases = f $ predAliases e }
mapRE f e = e { exprAliases = f $ exprAliases e }

cinfoError (Ci _ (Just e)) = e
cinfoError (Ci l _)        = errOther $ text $ "Cinfo:" ++ showPpr l


--------------------------------------------------------------------------------
--- Measures
--------------------------------------------------------------------------------
data Measure ty ctor = M {
    name :: LocSymbol
  , sort :: ty
  , eqns :: [Def ty ctor]
  } deriving (Data, Typeable)

data CMeasure ty
  = CM { cName :: LocSymbol
       , cSort :: ty
       }

data Def ty ctor 
  = Def { 
    measure :: LocSymbol
  , dparams :: [(Symbol, ty)]
  , ctor    :: ctor 
  , dsort   :: Maybe ty
  , binds   :: [(Symbol, Maybe ty)]
  , body    :: Body
  } deriving (Show, Data, Typeable)
deriving instance (Eq ctor, Eq ty) => Eq (Def ty ctor)

data Body
  = E Expr          -- ^ Measure Refinement: {v | v = e }
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  deriving (Show, Eq, Data, Typeable)

instance Subable (Measure ty ctor) where
  syms (M _ _ es)      = concatMap syms es
  substa f  (M n s es) = M n s $ substa f  <$> es
  substf f  (M n s es) = M n s $ substf f  <$> es
  subst  su (M n s es) = M n s $ subst  su <$> es

instance Subable (Def ty ctor) where
  syms (Def _ sp _ _ sb bd)  = (fst <$> sp) ++ (fst <$> sb) ++ syms bd
  substa f  (Def m p c t b bd) = Def m p c t b $ substa f  bd
  substf f  (Def m p c t b bd) = Def m p c t b $ substf f  bd
  subst  su (Def m p c t b bd) = Def m p c t b $ subst  su bd

instance Subable Body where
  syms (E e)       = syms e
  syms (P e)       = syms e
  syms (R s e)     = s:syms e

  substa f (E e)   = E $ substa f e
  substa f (P e)   = P $ substa f e
  substa f (R s e) = R s $ substa f e

  substf f (E e)   = E $ substf f e
  substf f (P e)   = P $ substf f e
  substf f (R s e) = R s $ substf f e

  subst su (E e)   = E $ subst su e
  subst su (P e)   = P $ subst su e
  subst su (R s e) = R s $ subst su e



data RClass ty
  = RClass { rcName    :: LocSymbol
           , rcSupers  :: [ty]
           , rcTyVars  :: [Symbol]
           , rcMethods :: [(LocSymbol,ty)]
           } deriving (Show)

instance Functor RClass where
  fmap f (RClass n ss tvs ms) = RClass n (fmap f ss) tvs (fmap (second f) ms)

------------------------------------------------------------------------
-- | Annotations -------------------------------------------------------
------------------------------------------------------------------------

newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Text, a)]) deriving (Generic)

data Annot t      = AnnUse t
                  | AnnDef t
                  | AnnRDf t
                  | AnnLoc SrcSpan

instance Monoid (AnnInfo a) where
  mempty                  = AI M.empty
  mappend (AI m1) (AI m2) = AI $ M.unionWith (++) m1 m2

instance Functor AnnInfo where
  fmap f (AI m) = AI (fmap (fmap (\(x, y) -> (x, f y))  ) m)


instance NFData a => NFData (AnnInfo a) where
  rnf (AI _) = ()

instance NFData (Annot a) where
  rnf (AnnDef _) = ()
  rnf (AnnRDf _) = ()
  rnf (AnnUse _) = ()
  rnf (AnnLoc _) = ()

------------------------------------------------------------------------
-- | Output ------------------------------------------------------------
------------------------------------------------------------------------

data Output a = O { o_vars   :: Maybe [String]
                  , o_errors :: ! [Error]
                  , o_types  :: !(AnnInfo a)
                  , o_templs :: !(AnnInfo a)
                  , o_bots   :: ![SrcSpan]
                  , o_result :: FixResult Error
                  } deriving (Generic)

emptyOutput = O Nothing [] mempty mempty [] mempty

instance Monoid (Output a) where
  mempty        = emptyOutput
  mappend o1 o2 = O { o_vars   = sortNub <$> mappend (o_vars   o1) (o_vars   o2)
                    , o_errors = sortNub  $  mappend (o_errors o1) (o_errors o2)
                    , o_types  =             mappend (o_types  o1) (o_types  o2)
                    , o_templs =             mappend (o_templs o1) (o_templs o2)
                    , o_bots   = sortNub  $  mappend (o_bots o1)   (o_bots   o2)
                    , o_result =             mappend (o_result o1) (o_result o2)
                    }

-----------------------------------------------------------
-- | KVar Profile -----------------------------------------
-----------------------------------------------------------

data KVKind
  = RecBindE
  | NonRecBindE
  | TypeInstE
  | PredInstE
  | LamE
  | CaseE
  | LetE
  deriving (Generic, Eq, Ord, Show, Enum, Data, Typeable)

instance Hashable KVKind where
  hashWithSalt i = hashWithSalt i. fromEnum

newtype KVProf = KVP (M.HashMap KVKind Int)

emptyKVProf :: KVProf
emptyKVProf = KVP M.empty

updKVProf :: KVKind -> [KVar] -> KVProf -> KVProf
updKVProf k kvs (KVP m) = KVP $ M.insert k (kn + length kvs) m
  where
    kn                  = M.lookupDefault 0 k m

instance NFData KVKind where
  rnf z = z `seq` ()

instance PPrint KVKind where
  pprint = text . show

instance PPrint KVProf where
  pprint (KVP m) = pprint $ M.toList m

instance NFData KVProf where
  rnf (KVP m) = rnf m `seq` ()

-- hasHole (toReft -> (Reft (_, rs))) = any isHole rs

hole :: Pred
hole = PKVar "HOLE" mempty

isHole :: Pred -> Bool
isHole (PKVar ("HOLE") _) = True
isHole _                  = False

hasHole :: Reftable r => r -> Bool
hasHole = any isHole . conjuncts . reftPred . toReft


-- isHole :: KVar -> Bool
-- isHole "HOLE" = True
-- isHole _      = False


-- classToRApp :: SpecType -> SpecType
-- classToRApp (RCls cl ts)
--   = RApp (RTyCon (classTyCon cl) def def) ts mempty mempty

instance Symbolic DataCon where
  symbol = symbol . dataConWorkId


instance PPrint DataCon where
  pprint = text . showPpr

instance Show DataCon where
  show = showpp
