{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TemplateHaskell            #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types (

  -- * Options
    Config (..)
  , HasConfig (..)
  , hasOpt

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
  , isClassRTyCon, isClassType, isEqType

  -- * Refinement Types
  , RType (..), Ref(..), RTProp, rPropP
  , RTyVar (..)
  , RTAlias (..)

  -- * Worlds
  , HSeg (..)
  , World (..)

  -- * Classes describing operations on `RTypes`
  , TyConable (..)
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
  , efoldReft, foldReft, foldReft'
  , mapReft, mapReftM
  , mapBot, mapBind

  -- * ???
  , Oblig(..)
  , ignoreOblig
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
  , ppEnv
  , ppEnvShort

  -- * Modules and Imports
  , ModName (..), ModType (..)
  , isSrcImport, isSpecImport
  , getModName, getModString

  -- * Refinement Type Aliases
  , RTEnv (..)
  , mapRT, mapRE

  -- * Errors and Error Messages
  , module Language.Haskell.Liquid.Types.Errors
  , Error
  , ErrorResult

  -- * Source information (associated with constraints)
  , Cinfo (..)

  -- * Measures
  , Measure (..)
  , CMeasure (..)
  , Def (..)
  , Body (..)
  , MSpec (..)

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
  , LogicMap(..), toLogicMap, eAppWithMap, LMap(..)

  -- * Refined Instances
  , RDEnv, DEnv(..), RInstance(..)

  -- * Ureftable Instances
  , UReftable(..)

  -- * String Literals
  , liquidBegin, liquidEnd

  , Axiom(..), HAxiom, LAxiom
  )
  where

import Prelude                          hiding  (error)
import SrcLoc                                   (noSrcSpan, SrcSpan)
import TyCon
import DataCon
import NameSet
import Module                                   (moduleNameFS)
import TypeRep                          hiding  (maybeParen, pprArrowChain)
import Var
import GHC                                      (HscEnv, ModuleName, moduleNameString)
import GHC.Generics
import CoreSyn (CoreBind, CoreExpr)
import PrelInfo         (isNumericClass)
import TysPrim          (eqPrimTyCon)
import TysWiredIn                               (listTyCon)

import            Control.Arrow                            (second)
import            Control.Monad                            (liftM, liftM2, liftM3, liftM4)
import qualified  Control.Exception
import qualified  Control.Monad.Error as Ex
import            Control.DeepSeq
import            Control.Applicative                      ((<$>))
import            Data.Bifunctor
import            Data.Bifunctor.TH
import            Data.Typeable                            (Typeable)
import            Data.Generics                            (Data)

import            Data.Monoid                              hiding ((<>))


import qualified  Data.Foldable as F
import            Data.Hashable
import qualified  Data.HashMap.Strict as M
import qualified  Data.HashSet as S
import            Data.Maybe                   (fromMaybe)
import            Data.Traversable             hiding (mapM)
import            Data.List                    (nub)
import            Data.Text                    (Text)
import qualified  Data.Text                    as T
import            Text.Parsec.Pos              (SourcePos)
import            Text.Parsec.Error            (ParseError)
import            Text.PrettyPrint.HughesPJ    hiding (first)
import            Text.Printf

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types      hiding (Error (..), SrcSpan, Result, Predicate, Def, R)
import           Language.Fixpoint.Types.Names      (symbolText, symbolString, funConName, listConName, tupConName)
import qualified Language.Fixpoint.Types.PrettyPrint as F
import           Language.Fixpoint.Types.Config     hiding (Config)

import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Variance
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.UX.Config
import Data.Default

-----------------------------------------------------------------------------
-- | Printer ----------------------------------------------------------------
-----------------------------------------------------------------------------

data PPEnv
  = PP { ppPs    :: Bool
       , ppTyVar :: Bool -- TODO if set to True all Bare fails
       , ppSs    :: Bool
       , ppShort :: Bool
       }
    deriving (Show)

ppEnv           = ppEnvPrintPreds
_ppEnvCurrent   = PP False False False False
ppEnvPrintPreds = PP False False False False
ppEnvShort pp   = pp { ppShort = True }



------------------------------------------------------------------
-- | GHC Information :  Code & Spec ------------------------------
------------------------------------------------------------------

data GhcInfo = GI {
    target   :: !FilePath
  , env      :: !HscEnv
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

instance HasConfig GhcInfo where
  getConfig = getConfig . spec


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
  , lazy       :: !(S.HashSet Var)             -- ^ Binders to IGNORE during termination checking
  , autosize   :: !(S.HashSet TyCon)             -- ^ Binders to IGNORE during termination checking
  , config     :: !Config                        -- ^ Configuration Options
  , exports    :: !NameSet                       -- ^ `Name`s exported by the module being verified
  , measures   :: [Measure SpecType DataCon]
  , tyconEnv   :: M.HashMap TyCon RTyCon
  , dicts      :: DEnv Var SpecType              -- ^ Dictionary Environment
  , axioms     :: [HAxiom]                       -- Axioms from axiomatized functions
  , logicMap   :: LogicMap
  , proofType  :: Maybe Type
  }

instance HasConfig GhcSpec where
  getConfig = config

data LogicMap = LM { logic_map :: M.HashMap Symbol LMap
                   , axiom_map :: M.HashMap Var Symbol
                   } deriving (Show)

instance Monoid LogicMap where
  mempty                        = LM M.empty M.empty
  mappend (LM x1 x2) (LM y1 y2) = LM (M.union x1 y1) (M.union x2 y2)

data LMap = LMap { lvar  :: Symbol
                 , largs :: [Symbol]
                 , lexpr :: Expr
                 }

instance Show LMap where
  show (LMap x xs e) = show x ++ " " ++ show xs ++ "\t|->\t" ++ show e


toLogicMap ls = mempty {logic_map = M.fromList $ map toLMap ls}
  where
    toLMap (x, xs, e) = (x, LMap {lvar = x, largs = xs, lexpr = e})

eAppWithMap lmap f es def
  | Just (LMap _ xs e) <- M.lookup (val f) (logic_map lmap), length xs == length es
  = subst (mkSubst $ zip xs es) e
  | Just (LMap _ xs e) <- M.lookup (val f) (logic_map lmap), isApp e
  = subst (mkSubst $ zip xs es) $ dropApp e (length xs - length es)
  | otherwise
  = def

dropApp e i | i <= 0 = e
dropApp (EApp e _) i = dropApp e (i-1)
dropApp _ _          = errorstar "impossible"

isApp (EApp (EVar _) (EVar _)) = True
isApp (EApp e (EVar _))        = isApp e
isApp _                        = False

data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![PVar RSort]
                     , freeLabelTy  :: ![Symbol]
                     , varianceTs   :: !VarianceInfo
                     , variancePs   :: !VarianceInfo
                     , sizeFun      :: !(Maybe (Symbol -> Expr))
                     } deriving (Generic, Data, Typeable)

data DataConP = DataConP { dc_loc     :: !SourcePos
                         , freeTyVars :: ![RTyVar]
                         , freePred   :: ![PVar RSort]
                         , freeLabels :: ![Symbol]
                         , tyConsts   :: ![SpecType] -- FIXME: WHAT IS THIS??
                         , tyArgs     :: ![(Symbol, SpecType)] -- FIXME: These are backwards, why??
                         , tyRes      :: !SpecType
                         , dc_locE    :: !SourcePos
                         } deriving (Generic, Data, Typeable)


-- | Which Top-Level Binders Should be Verified
data TargetVars = AllVars | Only ![Var]


--------------------------------------------------------------------
-- | Abstract Predicate Variables ----------------------------------
--------------------------------------------------------------------

data PVar t = PV
  { pname :: !Symbol
  , ptype :: !(PVKind t)
  , parg  :: !Symbol
  , pargs :: ![(t, Symbol, Expr)]
  } deriving (Generic, Data, Typeable, Show, Functor)

instance Eq (PVar t) where
  pv == pv' = pname pv == pname pv' {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _ _)  (PV n' _ _ _) = compare n n'

instance NFData t => NFData (PVar t)

instance Hashable (PVar a) where
  hashWithSalt i (PV n _ _ _) = hashWithSalt i n

pvType :: PVar t -> t
pvType p = case ptype p of
             PVProp t -> t
             PVHProp  -> panic Nothing "pvType on HProp-PVar"

data PVKind t
  = PVProp t
  | PVHProp
  deriving (Generic, Data, Typeable, Functor, F.Foldable, Traversable, Show)

instance NFData a => NFData (PVKind a)


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
  mempty                         = MkUReft mempty mempty mempty
  mappend (MkUReft x y z) (MkUReft x' y' z') = MkUReft (mappend x x') (mappend y y') (mappend z z')


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

instance NFData r => NFData (UReft r)

instance NFData Strata

instance NFData PrType

instance NFData RTyVar


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

instance NFData RTyCon

-- | Accessors for @RTyCon@


isClassRTyCon = isClassTyCon . rtc_tc
rTyConPVs     = rtc_pvars
rTyConPropVs  = filter isPropPV . rtc_pvars
isPropPV      = isProp . ptype

isEqType (RApp c _ _ _) = isEqual c
isEqType _              = False


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

instance NFData TyConInfo

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
  deriving (Generic, Data, Typeable, Functor)

instance (NFData c, NFData tv, NFData r) => NFData (RType c tv r)

ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t


-- | @Ref@ describes `Prop τ` and `HProp` arguments applied to type constructors.
--   For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
--   * the `RProp`  denoted by `{\h -> v > h}` to
--   * the `RTyCon` denoted by `[]`.
--   Thus, @Ref@ is used for abstract-predicate (arguments) that are associated
--   with _type constructors_ i.e. whose semantics are _dependent upon_ the data-type.
--   In contrast, the `Predicate` argument in `ur_pred` in the @UReft@ applies
--   directly to any type and has semantics _independent of_ the data-type.

data Ref τ t = RProp
  { rf_args :: [(Symbol, τ)]
  , rf_body :: t -- ^ Abstract refinement associated with `RTyCon`
  } deriving (Generic, Data, Typeable, Functor)

instance (NFData τ, NFData t) => NFData (Ref τ t)

rPropP τ r = RProp τ (RHole r)

-- | @RTProp@ is a convenient alias for @Ref@ that will save a bunch of typing.
--   In general, perhaps we need not expose @Ref@ directly at all.
type RTProp c tv r = Ref (RType c tv ()) (RType c tv r)


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
  = MkUReft { ur_reft   :: !r
            , ur_pred   :: !Predicate
            , ur_strata :: !Strata
            }
    deriving (Generic, Data, Typeable, Functor)

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
type RRProp r   = Ref       RSort (RRType r)


data Stratum    = SVar Symbol | SDiv | SWhnf | SFin
                  deriving (Generic, Data, Typeable, Eq)
instance NFData Stratum

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
  isEqual  :: c -> Bool

  isNumCls  :: c -> Bool
  isFracCls :: c -> Bool

  isClass   = const False
  isEqual   = const False
  isNumCls  = const False
  isFracCls = const False

-------------------------------------------------------------------------------
-- | TyConable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

-- MOVE TO TYPES
instance TyConable RTyCon where
  isFun      = isFunTyCon . rtc_tc
  isList     = (listTyCon ==) . rtc_tc
  isTuple    = TyCon.isTupleTyCon   . rtc_tc
  isClass    = isClassRTyCon
  isEqual    = (eqPrimTyCon ==) . rtc_tc
  ppTycon    = toFix

  isNumCls c  = maybe False isNumericClass    (tyConClass_maybe $ rtc_tc c)
  isFracCls c = maybe False isFractionalClass (tyConClass_maybe $ rtc_tc c)

-- MOVE TO TYPES
instance TyConable Symbol where
  isFun   s = funConName == s
  isList  s = listConName == s
  isTuple s = tupConName == s
  ppTycon   = text . symbolString

instance TyConable LocSymbol where
  isFun   = isFun . val
  isList  = isList . val
  isTuple = isTuple . val
  ppTycon = ppTycon . val


instance Eq RTyCon where
  x == y = rtc_tc x == rtc_tc y

instance Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c

instance Fixpoint Cinfo where
  toFix = text . showPpr . ci_loc

instance PPrint RTyCon where
  pprintTidy _ = text . showPpr . rtc_tc


instance Show RTyCon where
  show = showpp

--------------------------------------------------------------------------
-- | Refined Instances ---------------------------------------------------
--------------------------------------------------------------------------

data RInstance t = RI
  { riclass :: LocSymbol
  , ritype  :: t
  , risigs  :: [(LocSymbol, t)]
  } deriving Functor

newtype DEnv x ty = DEnv (M.HashMap x (M.HashMap Symbol ty)) deriving (Monoid)

type RDEnv = DEnv Var SpecType


--------------------------------------------------------------------------
-- | Values Related to Specifications ------------------------------------
--------------------------------------------------------------------------

data Axiom b s e = Axiom { aname  :: (Var, Maybe DataCon)
                         , abinds :: [b]
                         , atypes :: [s]
                         , alhs   :: e
                         , arhs   :: e
                         }
type HAxiom = Axiom Var Type CoreExpr
type LAxiom = Axiom Symbol Sort Expr


instance Show (Axiom Var Type CoreExpr) where
  show (Axiom (n, c) bs _ts lhs rhs) = "Axiom : " ++
                                       "\nFun Name: " ++ (showPpr n) ++
                                       "\nData Con: " ++ (showPpr c) ++
                                       "\nArguments:" ++ (showPpr bs)  ++
                                       -- "\nTypes    :" ++ (showPpr ts)  ++
                                       "\nLHS      :" ++ (showPpr lhs) ++
                                       "\nRHS      :" ++ (showPpr rhs)

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
   d1 == d2 = tycName d1 == tycName d2

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
    arrs = safeZip3WithError ("fromRTypeRep: " ++ show (length ty_binds, length ty_args, length ty_refts)) ty_binds ty_args ty_refts

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

safeBkArrow (RAllT _ _) = panic Nothing "safeBkArrow on RAllT"
safeBkArrow (RAllP _ _) = panic Nothing "safeBkArrow on RAllP"
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

addInvCond :: SpecType -> RReft -> SpecType
addInvCond t r'
  | isTauto $ ur_reft r' -- null rv
  = t
  | otherwise
  = fromRTypeRep $ trep {ty_res = RRTy [(x', tbd)] r OInv tbd}
  where
    trep = toRTypeRep t
    tbd  = ty_res trep
    r    = r' {ur_reft = Reft (v, rx)}
    su   = (v, EVar x')
    x'   = "xInv"
    rx   = PIff (EVar v) $ subst1 rv su
    Reft(v, rv) = ur_reft r'

-------------------------------------------

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

  ppTy _             = panic Nothing "ppTy on Strata"
  toReft _           = mempty
  params s           = [l | SVar l <- s]
  bot _              = []
  top _              = []

  ofReft = todo Nothing "TODO: Strata.ofReft"


class Reftable r => UReftable r where
  ofUReft :: UReft Reft -> r
  ofUReft (MkUReft r _ _) = ofReft r


instance UReftable (UReft Reft) where
   ofUReft r = r

instance UReftable () where
   ofUReft _ = mempty

instance (PPrint r, Reftable r) => Reftable (UReft r) where
  isTauto            = isTauto_ureft
  ppTy               = ppTy_ureft
  toReft (MkUReft r ps _)  = toReft r `meet` toReft ps
  params (MkUReft r _ _)   = params r
  bot (MkUReft r _ s)      = MkUReft (bot r) (Pr []) (bot s)
  top (MkUReft r p s)      = MkUReft (top r) (top p) s

  ofReft r = MkUReft (ofReft r) mempty mempty

isTauto_ureft u      = isTauto (ur_reft u) && isTauto (ur_pred u) -- && (isTauto $ ur_strata u)

ppTy_ureft u@(MkUReft r p s) d
  | isTauto_ureft  u  = d
  | otherwise         = ppr_reft r (ppTy p d) s

ppr_reft r d s       = braces (pprint v <+> colon <+> d <> ppr_str s <+> text "|" <+> pprint r')
  where
    r'@(Reft (v, _)) = toReft r

ppr_str [] = empty
ppr_str s  = text "^" <> pprint s

instance Subable r => Subable (UReft r) where
  syms (MkUReft r p _)     = syms r ++ syms p
  subst s (MkUReft r z l)  = MkUReft (subst s r) (subst s z) (subst s l)
  substf f (MkUReft r z l) = MkUReft (substf f r) (substf f z) (substf f l)
  substa f (MkUReft r z l) = MkUReft (substa f r) (substa f z) (substa f l)

instance (Reftable r, TyConable c) => Subable (RTProp c tv r) where
  syms (RProp  ss r)     = (fst <$> ss) ++ syms r

  subst su (RProp ss (RHole r)) = RProp ss (RHole (subst su r))
  subst su (RProp  ss t) = RProp ss (subst su <$> t)

  substf f (RProp ss (RHole r)) = RProp ss (RHole (substf f r))
  substf f (RProp  ss t) = RProp ss (substf f <$> t)

  substa f (RProp ss (RHole r)) = RProp ss (RHole (substa f r))
  substa f (RProp  ss t) = RProp ss (substa f <$> t)


instance (Subable r, Reftable r, TyConable c) => Subable (RType c tv r) where
  syms        = foldReft (\_ r acc -> syms r ++ acc) []
  substa f    = mapReft (substa f)
  substf f    = emapReft (substf . substfExcept f) []
  subst su    = emapReft (subst  . substExcept su) []
  subst1 t su = emapReft (\xs r -> subst1Except xs r su) [] t

instance Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = panic Nothing "No BOT instance for Predicate"
  -- NV: This does not print abstract refinements....
  -- HACK: Hiding to not render types in WEB DEMO. NEED TO FIX.
  ppTy r d | isTauto r        = d
           | not (ppPs ppEnv) = d
           | otherwise        = d <> (angleBrackets $ pprint r)

  toReft (Pr ps@(p:_))        = Reft (parg p, pAnd $ pToRef <$> ps)
  toReft _                    = mempty
  params                      = todo Nothing "TODO: instance of params for Predicate"

  ofReft = todo Nothing "TODO: Predicate.ofReft"

pToRef p = pApp (pname p) $ (EVar $ parg p) : (thd3 <$> pargs p)

pApp      :: Symbol -> [Expr] -> Expr
pApp p es = mkEApp (dummyLoc $ pappSym $ length es) (EVar p:es)

pappSym n  = symbol $ "papp" ++ show n

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

isTrivial t = foldReft (\_ r b -> isTauto r && b) True t

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
emapRef  f γ (RProp s (RHole r))  = RProp s $ RHole (f γ r)
emapRef  f γ (RProp  s t)         = RProp s $ emapReft f γ t

------------------------------------------------------------------------------------------------------
-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t
-- same as GhcMisc isBaseType

-- isBase :: RType a -> Bool

-- set all types to basic types, haskell `tx -> t` is translated to Arrow tx t
-- isBase _ = True

isBase (RAllT _ t)      = isBase t
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RFun _ _ _ _)   = False
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
mapRefM  f (RProp s t)         = liftM   (RProp s)      (mapReftM f t)


--------------------------------------------------------------------------------
-- foldReft :: (Reftable r, TyConable c) => (r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
-- foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) (\_ γ -> γ) emptySEnv

--------------------------------------------------------------------------------
foldReft :: (Reftable r, TyConable c) => (SEnv (RType c tv r) -> r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft f = foldReft' id (\γ _ -> f γ)

--------------------------------------------------------------------------------
foldReft' :: (Reftable r, TyConable c)
          => (RType c tv r -> b)
          -> (SEnv b -> Maybe (RType c tv r) -> r -> a -> a)
          -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft' g f = efoldReft (\_ _ -> []) g (\γ t r z -> f γ t r z) (\_ γ -> γ) emptySEnv



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
--     go γ z me@(RFun _ t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' (insertSEnv (rTypeValueVar me) (g me) γ) z ts) rs)

    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z me@(RRTy [] r _ t)          = f γ (Just me) r (go γ z t)
    go γ z me@(RRTy xts r _ t)          = f γ (Just me) r (go γ (go γ z (envtoType xts)) t)
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z
    go γ z me@(RHole r)                 = f γ (Just me) r z

    -- folding over Ref
    ho  γ z (RProp ss (RHole r))       = f (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) Nothing r z
    ho  γ z (RProp ss t)               = go (insertsSEnv γ ((mapSnd (g . ofRSort)) <$> ss)) z t

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
mapBotRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapBotRef f (RProp s t)    = RProp  s $ mapBot f t

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

mapBindRef f (RProp s (RHole r)) = RProp (mapFst f <$> s) (RHole r)
mapBindRef f (RProp s t)         = RProp (mapFst f <$> s) $ mapBind f t


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
stripAnnotationsRef (RProp s (RHole r)) = RProp s (RHole r)
stripAnnotationsRef (RProp s t)         = RProp s $ stripAnnotations t


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
        f (MkUReft r p _) = MkUReft r p [l]


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
  pprintTidy _ = text . show

instance PPrint Strata where
  pprintTidy _ [] = empty
  pprintTidy k ss = hsep (pprintTidy k <$> nub ss)

instance PPrint (PVar a) where
  pprintTidy _ = ppr_pvar

ppr_pvar :: PVar a -> Doc
ppr_pvar (PV s _ _ xts) = pprint s <+> hsep (pprint <$> dargs xts)
  where
    dargs               = map thd3 . takeWhile (\(_, x, y) -> EVar x /= y)


instance PPrint Predicate where
  pprintTidy _ (Pr [])  = text "True"
  pprintTidy k (Pr pvs) = hsep $ punctuate (text "&") (pprintTidy k <$> pvs)


-- | The type used during constraint generation, used
--   also to define contexts for errors, hence in this
--   file, and NOT in elsewhere. **DO NOT ATTEMPT TO MOVE**
--   Am splitting into
--   + global : many bindings, shared across all constraints
--   + local  : few bindings, relevant to particular constraints

data REnv = REnv
  { reGlobal :: M.HashMap Symbol SpecType -- ^ the "global" names for module
  , reLocal  :: M.HashMap Symbol SpecType -- ^ the "local" names for sub-exprs
  }

instance NFData REnv where
  rnf (REnv {}) = ()

------------------------------------------------------------------------
-- | Error Data Type ---------------------------------------------------
------------------------------------------------------------------------

type ErrorResult = FixResult UserError
type Error       = TError SpecType

instance NFData a => NFData (TError a)

------------------------------------------------------------------------
-- | Source Information Associated With Constraints --------------------
------------------------------------------------------------------------

data Cinfo    = Ci { ci_loc :: !SrcSpan
                   , ci_err :: !(Maybe Error)
                   }
                deriving (Eq, Ord, Generic)

instance NFData Cinfo

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
                   , exprAliases :: M.HashMap Symbol (RTAlias Symbol Expr)
                   }

instance Monoid RTEnv where
  (RTE ta1 ea1) `mappend` (RTE ta2 ea2)
    = RTE (ta1 `M.union` ta2) (ea1 `M.union` ea2)
  mempty = RTE M.empty M.empty

mapRT f e = e { typeAliases = f $ typeAliases e }
mapRE f e = e { exprAliases = f $ exprAliases e }


--------------------------------------------------------------------------------
--- Measures
--------------------------------------------------------------------------------
data Body
  = E Expr          -- ^ Measure Refinement: {v | v = e }
  | P Expr          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Expr   -- ^ Measure Refinement: {v | p}
  deriving (Show, Data, Typeable, Generic, Eq)

data Def ty ctor = Def
  { measure :: LocSymbol
  , dparams :: [(Symbol, ty)]
  , ctor    :: ctor
  , dsort   :: Maybe ty
  , binds   :: [(Symbol, Maybe ty)]
  , body    :: Body
  } deriving (Show, Data, Typeable, Generic, Eq, Functor)

data Measure ty ctor = M
  { name :: LocSymbol
  , sort :: ty
  , eqns :: [Def ty ctor]
  } deriving (Data, Typeable, Generic, Functor)

deriveBifunctor ''Def
deriveBifunctor ''Measure

data CMeasure ty = CM
  { cName :: LocSymbol
  , cSort :: ty
  } deriving (Data, Typeable, Generic, Functor)

instance PPrint Body where
  pprintTidy k (E e)   = pprintTidy k e
  pprintTidy k (P p)   = pprintTidy k p
  pprintTidy k (R v p) = braces (pprintTidy k v <+> "|" <+> pprintTidy k p)

instance PPrint a => PPrint (Def t a) where
  pprintTidy k (Def m p c _ bs body)
           = pprintTidy k m <+> pprintTidy k (fst <$> p) <+> cbsd <+> "=" <+> pprintTidy k body
    where
      cbsd = parens (pprintTidy k c <> hsep (pprintTidy k `fmap` (fst <$> bs)))

instance (PPrint t, PPrint a) => PPrint (Measure t a) where
  pprintTidy k (M n s eqs) =  pprintTidy k n <+> "::" <+> pprintTidy k s
                              $$ vcat (pprintTidy k `fmap` eqs)

instance PPrint (Measure t a) => Show (Measure t a) where
  show = showpp

instance PPrint t => PPrint (CMeasure t) where
  pprintTidy k (CM n s) =  pprintTidy k n <+> "::" <+> pprintTidy k s

instance PPrint (CMeasure t) => Show (CMeasure t) where
  show = showpp


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
           } deriving (Show, Functor)


------------------------------------------------------------------------
-- | Annotations -------------------------------------------------------
------------------------------------------------------------------------

newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Text, a)])
                    deriving (Data, Typeable, Generic, Functor)

data Annot t
  = AnnUse t
  | AnnDef t
  | AnnRDf t
  | AnnLoc SrcSpan
  deriving (Data, Typeable, Generic, Functor)

instance Monoid (AnnInfo a) where
  mempty                  = AI M.empty
  mappend (AI m1) (AI m2) = AI $ M.unionWith (++) m1 m2

instance NFData a => NFData (AnnInfo a)

instance NFData a => NFData (Annot a)

--------------------------------------------------------------------------------
-- | Output --------------------------------------------------------------------
--------------------------------------------------------------------------------

data Output a = O
  { o_vars   :: Maybe [String]
  , o_errors :: ![UserError]
  , o_types  :: !(AnnInfo a)
  , o_templs :: !(AnnInfo a)
  , o_bots   :: ![SrcSpan]
  , o_result :: ErrorResult
  } deriving (Typeable, Generic, Functor)

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

--------------------------------------------------------------------------------
-- | KVar Profile --------------------------------------------------------------
--------------------------------------------------------------------------------

data KVKind
  = RecBindE
  | NonRecBindE
  | TypeInstE
  | PredInstE
  | LamE
  | CaseE
  | LetE
  deriving (Generic, Eq, Ord, Show, Enum, Data, Typeable)

instance Hashable KVKind

newtype KVProf = KVP (M.HashMap KVKind Int) deriving (Generic)

emptyKVProf :: KVProf
emptyKVProf = KVP M.empty

updKVProf :: KVKind -> Kuts -> KVProf -> KVProf
updKVProf k kvs (KVP m) = KVP $ M.insert k (kn + n) m
  where
    kn                  = M.lookupDefault 0 k m
    n                   = S.size $ ksVars kvs


instance NFData KVKind

instance PPrint KVKind where
  pprintTidy _ = text . show

instance PPrint KVProf where
  pprintTidy _ (KVP m) = pprint $ M.toList m

instance NFData KVProf

hole :: Expr
hole = PKVar "HOLE" mempty

isHole :: Expr -> Bool
isHole (PKVar ("HOLE") _) = True
isHole _                  = False

hasHole :: Reftable r => r -> Bool
hasHole = any isHole . conjuncts . reftPred . toReft

-- classToRApp :: SpecType -> SpecType
-- classToRApp (RCls cl ts)
--   = RApp (RTyCon (classTyCon cl) def def) ts mempty mempty

instance Symbolic DataCon where
  symbol = symbol . dataConWorkId


instance PPrint DataCon where
  pprintTidy _ = text . showPpr

instance Show DataCon where
  show = showpp


liquidBegin :: String
liquidBegin = ['{', '-', '@']

liquidEnd :: String
liquidEnd = ['@', '-', '}']

data MSpec ty ctor = MSpec
  { ctorMap  :: M.HashMap Symbol [Def ty ctor]
  , measMap  :: M.HashMap LocSymbol (Measure ty ctor)
  , cmeasMap :: M.HashMap LocSymbol (Measure ty ())
  , imeas    :: ![Measure ty ctor]
  } deriving (Data, Typeable, Generic, Functor)

instance Bifunctor MSpec   where
  first f (MSpec c m cm im) = MSpec (fmap (fmap (first f)) c)
                                    (fmap (first f) m)
                                    (fmap (first f) cm)
                                    (fmap (first f) im)
  second                    = fmap

instance (PPrint t, PPrint a) => PPrint (MSpec t a) where
  pprintTidy k =  vcat . fmap (pprintTidy k) . fmap snd . M.toList . measMap

instance (Show ty, Show ctor, PPrint ctor, PPrint ty) => Show (MSpec ty ctor) where
  show (MSpec ct m cm im)
    = "\nMSpec:\n" ++
      "\nctorMap:\t "  ++ show ct ++
      "\nmeasMap:\t "  ++ show m  ++
      "\ncmeasMap:\t " ++ show cm ++
      "\nimeas:\t "    ++ show im ++
      "\n"

instance Eq ctor => Monoid (MSpec ty ctor) where
  mempty = MSpec M.empty M.empty M.empty []

  (MSpec c1 m1 cm1 im1) `mappend` (MSpec c2 m2 cm2 im2)
    | null dups
    = MSpec (M.unionWith (++) c1 c2) (m1 `M.union` m2)
           (cm1 `M.union` cm2) (im1 ++ im2)
    | otherwise
    = panic Nothing $ err (head dups)
    where dups = [(k1, k2) | k1 <- M.keys m1 , k2 <- M.keys m2, val k1 == val k2]
          err (k1, k2) = printf "\nDuplicate Measure Definitions for %s\n%s" (showpp k1) (showpp $ map loc [k1, k2])

--------------------------------------------------------------------------------
-- Nasty PP stuff
--------------------------------------------------------------------------------

instance PPrint RTyVar where
  pprintTidy _ (RTV α)
   | ppTyVar ppEnv  = ppr_tyvar α
   | otherwise      = ppr_tyvar_short α
   where
    ppr_tyvar       = text . tvId
    ppr_tyvar_short = text . showPpr

instance (PPrint r, Reftable r, PPrint t, PPrint (RType c tv r)) => PPrint (Ref t (RType c tv r)) where
  pprintTidy k (RProp ss (RHole s)) = ppRefArgs k (fst <$> ss) <+> pprintTidy k s
  pprintTidy k (RProp ss s)         = ppRefArgs k (fst <$> ss) <+> pprintTidy k (fromMaybe mempty (stripRTypeBase s))


ppRefArgs :: Tidy -> [Symbol] -> Doc
ppRefArgs _ [] = empty
ppRefArgs k ss = text "\\" <> hsep (ppRefSym k <$> ss ++ [vv Nothing]) <+> "->"

ppRefSym _ "" = text "_"
ppRefSym k s  = pprintTidy k s
