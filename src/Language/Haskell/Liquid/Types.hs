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
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE TupleSections              #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types (

  -- * Options
    Config (..)
  , HasConfig (..)

  -- * Ghc Information
  , GhcInfo (..)
  , GhcSpec (..)
  , TargetVars (..)

  -- * F.Located Things
  , F.Located (..)
  , F.dummyLoc

  -- * Symbols
  , F.LocSymbol
  , F.LocText

  -- * Default unknown name
  , F.dummyName
  , F.isDummy

  -- * Bare Type Constructors and Variables
  , BTyCon(..)
  , mkBTyCon, mkClassBTyCon, mkPromotedBTyCon
  , isClassBTyCon
  , BTyVar(..)

  -- * Refined Type Constructors
  , RTyCon (RTyCon, rtc_tc, rtc_info)
  , TyConInfo(..), defaultTyConInfo
  , rTyConPVs
  , rTyConPropVs
  , isClassRTyCon, isClassType, isEqType, isRVar, isBool

  -- * Refinement Types
  , RType (..), Ref(..), RTProp, rPropP
  , RTyVar (..)
  , RTAlias (..)
  , OkRT
  , lmapEAlias

  -- * Worlds
  , HSeg (..)
  , World (..)

  -- * Classes describing operations on `RTypes`
  , TyConable (..)
  , SubsTy (..)

  -- * Type Variables
  , RTVar (..), RTVInfo (..)
  , makeRTVar, mapTyVarValue
  , dropTyVarInfo, rTVarToBind

  -- * Predicate Variables
  , PVar (PV, pname, parg, ptype, pargs), isPropPV, pvType
  , PVKind (..)
  , Predicate (..)

  -- * Refinements
  , UReft(..)

  -- * Parse-time entities describing refined data types
  , SizeFun  (..), szFun
  , DataDecl (..)
  , DataName (..), dataNameSymbol
  , DataCtor (..)
  , DataConP (..)
  , HasDataDecl (..), hasDecl
  , DataDeclKind (..)
  , TyConP   (..)

  -- * Pre-instantiated RType
  , RRType, RRProp
  , BRType, BRProp
  , BSort, BPVar
  , RTVU, PVU

  -- * Instantiated RType
  , BareType, PrType
  , SpecType, SpecProp
  , SpecRep
  , LocBareType, LocSpecType
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
  , mapReft, mapReftM, mapPropM
  , mapBot, mapBind
  , foldRType


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
  , topRTypeBase

  -- * Class for values that can be pretty printed
  , F.PPrint (..)
  , F.pprint
  , F.showpp

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
  , RDEnv, DEnv(..), RInstance(..), RISig(..)

  -- * Ureftable Instances
  , UReftable(..)

  -- * String Literals
  , liquidBegin, liquidEnd

  , Axiom(..), HAxiom, AxiomEq -- (..)

  , rtyVarUniqueSymbol, tyVarUniqueSymbol, rtyVarType
  )
  where

import           Class
import           CoreSyn                                (CoreBind, CoreExpr)
import           Data.String
import           DataCon
import           GHC                                    (HscEnv, ModuleName, moduleNameString, getName)
import           GHC.Generics
import           Module                                 (moduleNameFS)
import           NameSet
import           PrelInfo                               (isNumericClass)
import Prelude                          hiding  (error)
import           SrcLoc                                 (SrcSpan)
import           TyCon
import           Type                                   (getClassPredTys_maybe)
import           Language.Haskell.Liquid.GHC.TypeRep                          hiding  (maybeParen, pprArrowChain)
import           TysPrim                                (eqPrimTyCon)
import           TysWiredIn                             (listTyCon, boolTyCon)
import           Var

import           Control.Monad                          (liftM, liftM2, liftM3, liftM4)
import           Control.DeepSeq
import           Data.Bifunctor
--import           Data.Bifunctor.TH
import           Data.Typeable                          (Typeable)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import qualified Data.Foldable                          as F
import           Data.Hashable
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import           Data.Maybe                             (fromMaybe, mapMaybe)

import           Data.List                              (foldl', nub)
import           Data.Text                              (Text)



import           Text.PrettyPrint.HughesPJ              hiding (first)
import           Text.Printf

import           Language.Fixpoint.Misc
-- import           Language.Fixpoint.Types                hiding (SmtSort (..), DataDecl, Error, SrcSpan, Result, Predicate, R)

import qualified Language.Fixpoint.Types as F


import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.UX.Config
import           Data.Default

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

ppEnv :: PPEnv
ppEnv           = ppEnvCurrent

ppEnvCurrent :: PPEnv
ppEnvCurrent    = PP False False False False

_ppEnvPrintPreds :: PPEnv
_ppEnvPrintPreds = PP True False False False

ppEnvShort :: PPEnv -> PPEnv
ppEnvShort pp   = pp { ppShort = True }



------------------------------------------------------------------
-- | GHC Information :  Code & Spec ------------------------------
------------------------------------------------------------------

data GhcInfo = GI
  { target   :: !FilePath       -- ^ Source file for module
  , targetMod:: !ModuleName     -- ^ Name for module
  , env      :: !HscEnv         -- ^ GHC Env used to resolve names for module
  , cbs      :: ![CoreBind]     -- ^ Source Code
  , derVars  :: ![Var]          -- ^ ?
  , impVars  :: ![Var]          -- ^ Binders that are _read_ in module (but not defined?)
  , defVars  :: ![Var]          -- ^ (Top-level) binders that are _defined_ in module
  , useVars  :: ![Var]          -- ^ Binders that are _read_ in module
--   , tyCons   :: ![TyCon]        -- ^ Types that are defined inside module
  , hqFiles  :: ![FilePath]     -- ^ Imported .hqual files
  , imports  :: ![String]       -- ^ ??? dead?
  , includes :: ![FilePath]     -- ^ ??? dead?
  , spec     :: !GhcSpec        -- ^ All specification information for module
  }

instance HasConfig GhcInfo where
  getConfig = getConfig . spec


type Expr      = F.Expr
type Symbol    = F.Symbol
type Qualifier = F.Qualifier
-- | The following is the overall type for /specifications/ obtained from
-- parsing the target source and dependent libraries

data GhcSpec = SP {
    gsTySigs   :: ![(Var, LocSpecType)]          -- ^ Asserted Reftypes
  , gsAsmSigs  :: ![(Var, LocSpecType)]          -- ^ Assumed Reftypes
  , gsInSigs   :: ![(Var, LocSpecType)]          -- ^ Auto generated Signatures
  , gsCtors    :: ![(Var, LocSpecType)]          -- ^ Data Constructor Measure Sigs
  , gsLits     :: ![(Symbol, LocSpecType)]       -- ^ Literals/Constants
                                                 -- e.g. datacons: EQ, GT, string lits: "zombie",...
  , gsMeas     :: ![(Symbol, LocSpecType)]       -- ^ Measure Types
                                                 -- eg.  len :: [a] -> Int
  , gsInvariants :: ![(Maybe Var, LocSpecType)]  -- ^ Data Type Invariants that came from the definition of var measure
                                                 -- eg.  forall a. {v: [a] | len(v) >= 0}
  , gsIaliases   :: ![(LocSpecType, LocSpecType)]-- ^ Data Type Invariant Aliases
  , gsDconsP     :: ![F.Located DataCon]           -- ^ Predicated Data-Constructors
                                                 -- e.g. see tests/pos/Map.hs
  , gsTconsP     :: ![(TyCon, TyConP)]           -- ^ Predicated Type-Constructors
                                                 -- eg.  see tests/pos/Map.hs
  , gsFreeSyms   :: ![(Symbol, Var)]             -- ^ List of `Symbol` free in spec and corresponding GHC var
                                                 -- eg. (Cons, Cons#7uz) from tests/pos/ex1.hs
  , gsTcEmbeds   :: F.TCEmb TyCon                  -- ^ How to embed GHC Tycons into fixpoint sorts
                                                 -- e.g. "embed Set as Set_set" from include/Data/Set.spec
  , gsQualifiers :: ![Qualifier]                 -- ^ Qualifiers in Source/Spec files
                                                 -- e.g tests/pos/qualTest.hs
  , gsADTs       :: ![F.DataDecl]                -- ^ ADTs extracted from Haskell 'data' definitions
  , gsTgtVars    :: ![Var]                       -- ^ Top-level Binders To Verify (empty means ALL binders)
  , gsDecr       :: ![(Var, [Int])]              -- ^ Lexicographically ordered size witnesses for termination
  , gsTexprs     :: ![(Var, [F.Located Expr])]     -- ^ Lexicographically ordered expressions for termination
  , gsNewTypes   :: ![(TyCon, LocSpecType)]      -- ^ Mapping of 'newtype' type constructors with their refined types.
  , gsLvars      :: !(S.HashSet Var)             -- ^ Variables that should be checked in the environment they are used
  , gsLazy       :: !(S.HashSet Var)             -- ^ Binders to IGNORE during termination checking
  , gsAutosize   :: !(S.HashSet TyCon)           -- ^ Binders to IGNORE during termination checking
  , gsAutoInst   :: !(M.HashMap Var (Maybe Int))  -- ^ Binders to expand with automatic axiom instances maybe with specified fuel
  , gsConfig     :: !Config                      -- ^ Configuration Options
  , gsExports    :: !NameSet                       -- ^ `Name`s exported by the module being verified
  , gsMeasures   :: [Measure SpecType DataCon]
  , gsTyconEnv   :: M.HashMap TyCon RTyCon
  , gsDicts      :: DEnv Var SpecType              -- ^ Dictionary Environment
  , gsAxioms     :: [AxiomEq]                      -- ^ Axioms from reflected functions
  , gsReflects   :: [Var]                          -- ^ Binders for reflected functions
  , gsLogicMap   :: LogicMap
  , gsProofType  :: Maybe Type
  , gsRTAliases  :: !RTEnv                         -- ^ Refinement type aliases
  }

instance HasConfig GhcSpec where
  getConfig = gsConfig

-- axiom_map ===> lmVarSyms

-- [NOTE:LIFTED-VAR-SYMBOLS]: Following NOTE:REFLECT-IMPORTS, by default
-- each (lifted) `Var` is mapped to its `Symbol` via the `Symbolic Var`
-- instance. For _generated_ vars, we may want a custom name e.g. see
--   tests/pos/NatClass.hs
-- and we maintain that map in `lmVarSyms` with the `Just s` case.
-- Ideally, this bandaid should be replaced so we don't have these
-- hacky corner cases.

data LogicMap = LM
  { lmSymDefs  :: M.HashMap Symbol LMap        -- ^ Map from symbols to equations they define
  , lmVarSyms  :: M.HashMap Var (Maybe Symbol) -- ^ Map from (lifted) Vars to `Symbol`; see:
                                              --   NOTE:LIFTED-VAR-SYMBOLS and NOTE:REFLECT-IMPORTs
  } deriving (Show)

instance Monoid LogicMap where
  mempty                        = LM M.empty M.empty
  mappend (LM x1 x2) (LM y1 y2) = LM (M.union x1 y1) (M.union x2 y2)

data LMap = LMap
  { lmVar  :: F.LocSymbol
  , lmArgs :: [Symbol]
  , lmExpr :: Expr
  }

instance Show LMap where
  show (LMap x xs e) = show x ++ " " ++ show xs ++ "\t |-> \t" ++ show e

toLogicMap :: [(F.LocSymbol, [Symbol], Expr)] -> LogicMap
toLogicMap ls = mempty {lmSymDefs = M.fromList $ map toLMap ls}
  where
    toLMap (x, ys, e) = (F.val x, LMap {lmVar = x, lmArgs = ys, lmExpr = e})

eAppWithMap :: LogicMap -> F.Located Symbol -> [Expr] -> Expr -> Expr
eAppWithMap lmap f es def
  | Just (LMap _ xs e) <- M.lookup (F.val f) (lmSymDefs lmap)
  , length xs == length es
  = F.subst (F.mkSubst $ zip xs es) e
  | Just (LMap _ xs e) <- M.lookup (F.val f) (lmSymDefs lmap)
  , isApp e
  = F.subst (F.mkSubst $ zip xs es) $ dropApp e (length xs - length es)
  | otherwise
  = def

dropApp :: Expr -> Int -> Expr
dropApp e i | i <= 0 = e
dropApp (F.EApp e _) i = dropApp e (i-1)
dropApp _ _          = errorstar "impossible"

isApp :: Expr -> Bool
isApp (F.EApp (F.EVar _) (F.EVar _)) = True
isApp (F.EApp e (F.EVar _))          = isApp e
isApp _                              = False

data TyConP = TyConP
  { ty_loc       :: !F.SourcePos
  , freeTyVarsTy :: ![RTyVar]
  , freePredTy   :: ![PVar RSort]
  , freeLabelTy  :: ![Symbol]
  , varianceTs   :: !VarianceInfo
  , variancePs   :: !VarianceInfo
  , sizeFun      :: !(Maybe SizeFun)
  } deriving (Generic, Data, Typeable)

-- TODO: just use Located instead of dc_loc, dc_locE
data DataConP = DataConP
  { dc_loc     :: !F.SourcePos
  , freeTyVars :: ![RTyVar]               -- ^ Type parameters
  , freePred   :: ![PVar RSort]           -- ^ Abstract Refinement parameters
  , freeLabels :: ![Symbol]               -- ^ ? strata stuff
  , tyConstrs  :: ![SpecType]             -- ^ ? Class constraints (via `dataConStupidTheta`)
  , tyArgs     :: ![(Symbol, SpecType)]   -- ^ Value parameters
  , tyRes      :: !SpecType               -- ^ Result type
  -- , tyData     :: !SpecType               -- ^ The 'generic' ADT, see [NOTE:DataCon-Data]
  , dcpIsGadt  :: !Bool                   -- ^ Was this specified in GADT style (if so, DONT use function names as fields)
  , dcpModule  :: !F.Symbol               -- ^ Which module was this defined in
  , dc_locE    :: !F.SourcePos
  } deriving (Generic, Data, Typeable)

-- | [NOTE:DataCon-Data] for each 'DataConP' we also
--   store the type of the constructed data. This is
--   *the same as* 'tyRes' for *vanilla* ADTs
--   (e.g. List, Maybe etc.) but may differ for GADTs.
--   For example,
--
--      data Thing a where
--        X  :: Thing Int
--        Y  :: Thing Bool
--
--   Here the 'DataConP' associated with 'X' (resp. 'Y')
--   has 'tyRes' corresponding to 'Thing Int' (resp. 'Thing Bool'),
--   but in both cases, the 'tyData' should be 'Thing a'.
--


instance F.Loc DataConP where
  srcSpan d = F.SS (dc_loc d) (dc_locE d)

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

instance B.Binary t => B.Binary (PVar t)
instance NFData t   => NFData   (PVar t)

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

instance B.Binary a => B.Binary (PVKind a)
instance NFData a   => NFData   (PVKind a)


--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

type UsedPVar      = PVar ()

newtype Predicate  = Pr [UsedPVar] deriving (Generic, Data, Typeable)

instance B.Binary Predicate

instance NFData Predicate where
  rnf _ = ()

instance Monoid Predicate where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Monoid a) => Monoid (UReft a) where
  mempty                         = MkUReft mempty mempty mempty
  mappend (MkUReft x y z) (MkUReft x' y' z') = MkUReft (mappend x x') (mappend y y') (mappend z z')


pdTrue :: Predicate
pdTrue         = Pr []

pdAnd :: Foldable t => t Predicate -> Predicate
pdAnd ps       = Pr (nub $ concatMap pvars ps)

pvars :: Predicate -> [UsedPVar]
pvars (Pr pvs) = pvs

instance F.Subable UsedPVar where
  syms pv         = [ y | (_, x, F.EVar y) <- pargs pv, x /= y ]
  subst s pv      = pv { pargs = mapThd3 (F.subst s)  <$> pargs pv }
  substf f pv     = pv { pargs = mapThd3 (F.substf f) <$> pargs pv }
  substa f pv     = pv { pargs = mapThd3 (F.substa f) <$> pargs pv }


instance F.Subable Predicate where
  syms     (Pr pvs) = concatMap F.syms   pvs
  subst  s (Pr pvs) = Pr (F.subst s  <$> pvs)
  substf f (Pr pvs) = Pr (F.substf f <$> pvs)
  substa f (Pr pvs) = Pr (F.substa f <$> pvs)

instance F.Subable Qualifier where
  syms   = F.syms . F.qBody
  subst  = mapQualBody . F.subst
  substf = mapQualBody . F.substf
  substa = mapQualBody . F.substa

mapQualBody :: (Expr -> Expr) -> Qualifier -> Qualifier
mapQualBody f q = q { F.qBody = f (F.qBody q) }

instance NFData r => NFData (UReft r)


newtype BTyVar = BTV Symbol deriving (Show, Generic, Data, Typeable)

newtype RTyVar = RTV TyVar deriving (Generic, Data, Typeable)

instance Eq BTyVar where
  (BTV x) == (BTV y) = x == y

instance Ord BTyVar where
  compare (BTV x) (BTV y) = compare x y

instance IsString BTyVar where
  fromString = BTV . fromString

instance B.Binary BTyVar
instance Hashable BTyVar
instance NFData   BTyVar
instance NFData   RTyVar

instance F.Symbolic BTyVar where
  symbol (BTV tv) = tv

instance F.Symbolic RTyVar where
  symbol (RTV tv) = F.symbol . getName $ tv

data BTyCon = BTyCon
  { btc_tc    :: !F.LocSymbol    -- ^ TyCon name with location information
  , btc_class :: !Bool         -- ^ Is this a class type constructor?
  , btc_prom  :: !Bool         -- ^ Is Promoted Data Con?
  }
  deriving (Generic, Data, Typeable)

instance B.Binary BTyCon

data RTyCon = RTyCon
  { rtc_tc    :: TyCon         -- ^ GHC Type Constructor
  , rtc_pvars :: ![RPVar]      -- ^ Predicate Parameters
  , rtc_info  :: !TyConInfo    -- ^ TyConInfo
  }
  deriving (Generic, Data, Typeable)

instance F.Symbolic BTyCon where
  symbol = F.val . btc_tc

instance NFData BTyCon

instance NFData RTyCon

rtyVarUniqueSymbol  :: RTyVar -> Symbol
rtyVarUniqueSymbol (RTV tv) = tyVarUniqueSymbol tv

tyVarUniqueSymbol :: TyVar -> Symbol
tyVarUniqueSymbol tv = F.symbol $ show (getName tv) ++ "_" ++ show (varUnique tv)

rtyVarType :: RTyVar -> Type
rtyVarType (RTV v) = TyVarTy v

mkBTyCon :: F.LocSymbol -> BTyCon
mkBTyCon x = BTyCon x False False

mkClassBTyCon :: F.LocSymbol -> BTyCon
mkClassBTyCon x = BTyCon x True False

mkPromotedBTyCon :: F.LocSymbol -> BTyCon
mkPromotedBTyCon x = BTyCon x False True


-- | Accessors for @RTyCon@

isBool :: RType RTyCon t t1 -> Bool
isBool (RApp (RTyCon{rtc_tc = c}) _ _ _) = c == boolTyCon
isBool _                                 = False

isRVar :: RType c tv r -> Bool
isRVar (RVar _ _) = True
isRVar _          = False

isClassBTyCon :: BTyCon -> Bool
isClassBTyCon = btc_class

isClassRTyCon :: RTyCon -> Bool
isClassRTyCon x = (isClassTyCon $ rtc_tc x) || (rtc_tc x == eqPrimTyCon)

rTyConPVs :: RTyCon -> [RPVar]
rTyConPVs     = rtc_pvars

rTyConPropVs :: RTyCon -> [PVar RSort]
rTyConPropVs  = filter isPropPV . rtc_pvars

isPropPV :: PVar t -> Bool
isPropPV      = isProp . ptype

isEqType :: TyConable c => RType c t t1 -> Bool
isEqType (RApp c _ _ _) = isEqual c
isEqType _              = False


isClassType :: TyConable c => RType c t t1 -> Bool
isClassType (RApp c _ _ _) = isClass c
isClassType _              = False

-- rTyConPVHPs = filter isHPropPV . rtc_pvars
-- isHPropPV   = not . isPropPV

isProp :: PVKind t -> Bool
isProp (PVProp _) = True
isProp _          = False


defaultTyConInfo :: TyConInfo
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
  { varianceTyArgs  :: !VarianceInfo      -- ^ variance info for type variables
  , variancePsArgs  :: !VarianceInfo      -- ^ variance info for predicate variables
  , sizeFunction    :: !(Maybe SizeFun)   -- ^ logical UNARY function that computes the size of the structure
  } deriving (Generic, Data, Typeable)

instance NFData TyConInfo

instance Show TyConInfo where
  show (TyConInfo x y _) = show x ++ "\n" ++ show y

--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------
type RTVU c tv = RTVar tv (RType c tv ())
type PVU  c tv = PVar     (RType c tv ())

instance Show tv => Show (RTVU c tv) where
  show (RTVar t _) = show t

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
      rt_tvbind :: !(RTVU c tv) -- RTVar tv (RType c tv ()))
    , rt_ty     :: !(RType c tv r)
    }

  -- | "forall x y <z :: Nat, w :: Int> . TYPE"
  --               ^^^^^^^^^^^^^^^^^^^ (rt_pvbind)
  | RAllP {
      rt_pvbind :: !(PVU c tv)  -- ar (RType c tv ()))
    , rt_ty     :: !(RType c tv r)
    }

  -- | "forall <z w> . TYPE"
  --           ^^^^^ (rt_sbind)
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

  | RExprArg (F.Located Expr)                   -- ^ For expression arguments to type aliases
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

instance (B.Binary c, B.Binary tv, B.Binary r) => B.Binary (RType c tv r)
instance (NFData c, NFData tv, NFData r)       => NFData (RType c tv r)

ignoreOblig :: RType t t1 t2 -> RType t t1 t2
ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t


makeRTVar :: tv -> RTVar tv s
makeRTVar a = RTVar a RTVNoInfo

instance (Eq tv) => Eq (RTVar tv s) where
  t1 == t2 = (ty_var_value t1) == (ty_var_value t2)

data RTVar tv s = RTVar
  { ty_var_value :: tv
  , ty_var_info  :: RTVInfo s
  } deriving (Generic, Data, Typeable)

mapTyVarValue :: (tv1 -> tv2) -> RTVar tv1 s -> RTVar tv2 s
mapTyVarValue f v = v {ty_var_value = f $ ty_var_value v}

dropTyVarInfo :: RTVar tv s1 -> RTVar tv s2
dropTyVarInfo v = v{ty_var_info = RTVNoInfo}

data RTVInfo s
  = RTVNoInfo
  | RTVInfo { rtv_name   :: Symbol
            , rtv_kind   :: s
            , rtv_is_val :: Bool
            } deriving (Generic, Data, Typeable, Functor)


rTVarToBind :: RTVar RTyVar s  -> Maybe (Symbol, s)
rTVarToBind = go . ty_var_info
  where
    go (RTVInfo {..}) | rtv_is_val = Just (rtv_name, rtv_kind)
    go _                           = Nothing

ty_var_is_val :: RTVar tv s -> Bool
ty_var_is_val = rtvinfo_is_val . ty_var_info

rtvinfo_is_val :: RTVInfo s -> Bool
rtvinfo_is_val RTVNoInfo      = False
rtvinfo_is_val (RTVInfo {..}) = rtv_is_val

instance (B.Binary tv, B.Binary s) => B.Binary (RTVar tv s)
instance (NFData tv, NFData s)     => NFData   (RTVar tv s)
instance (NFData s)                => NFData   (RTVInfo s)
instance (B.Binary s)              => B.Binary (RTVInfo s)

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

instance (B.Binary τ, B.Binary t) => B.Binary (Ref τ t)
instance (NFData τ,   NFData t)   => NFData   (Ref τ t)

rPropP :: [(Symbol, τ)] -> r -> Ref τ (RType c tv r)
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

data UReft r = MkUReft
  { ur_reft   :: !r
  , ur_pred   :: !Predicate
  , ur_strata :: !Strata
  }
  deriving (Generic, Data, Typeable, Functor, Foldable, Traversable)

instance B.Binary r => B.Binary (UReft r)

type BRType     = RType BTyCon BTyVar
type RRType     = RType RTyCon RTyVar
type RRep       = RTypeRep RTyCon RTyVar

type BSort      = BRType    ()
type RSort      = RRType    ()

type BPVar      = PVar      BSort
type RPVar      = PVar      RSort

type RReft       = UReft     F.Reft
type PrType      = RRType    Predicate
type BareType    = BRType    RReft
type SpecType    = RRType    RReft
type SpecRep     = RRep      RReft
type SpecProp    = RRProp    RReft
type RRProp r    = Ref       RSort (RRType r)
type BRProp r    = Ref       BSort (BRType r)

type LocBareType = F.Located BareType
type LocSpecType = F.Located SpecType

data Stratum    = SVar Symbol | SDiv | SWhnf | SFin
                  deriving (Generic, Data, Typeable, Eq)

instance NFData   Stratum
instance B.Binary Stratum

type Strata = [Stratum]

isSVar :: Stratum -> Bool
isSVar (SVar _) = True
isSVar _        = False

instance {-# OVERLAPPING #-} Monoid Strata where
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


-- Should just make this a @Pretty@ instance but its too damn tedious
-- to figure out all the constraints.

type OkRT c tv r = ( TyConable c
                   , F.PPrint tv, F.PPrint c, F.PPrint r
                   , F.Reftable r, F.Reftable (RTProp c tv ()), F.Reftable (RTProp c tv r)
                   , Eq c, Eq tv
                   , Hashable tv
                   )

-------------------------------------------------------------------------------
-- | TyConable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance TyConable RTyCon where
  isFun      = isFunTyCon . rtc_tc
  isList     = (listTyCon ==) . rtc_tc
  isTuple    = TyCon.isTupleTyCon   . rtc_tc
  isClass    = isClassRTyCon
  isEqual    = (eqPrimTyCon ==) . rtc_tc
  ppTycon    = F.toFix

  isNumCls c  = maybe False (isClassOrSubClass isNumericClass)
                (tyConClass_maybe $ rtc_tc c)
  isFracCls c = maybe False (isClassOrSubClass isFractionalClass)
                (tyConClass_maybe $ rtc_tc c)


instance TyConable TyCon where
  isFun      = isFunTyCon
  isList     = (listTyCon ==)
  isTuple    = TyCon.isTupleTyCon
  isClass c  = isClassTyCon c || c == eqPrimTyCon
  isEqual    = (eqPrimTyCon ==)
  ppTycon    = text . showPpr

  isNumCls c  = maybe False (isClassOrSubClass isNumericClass)
                (tyConClass_maybe $ c)
  isFracCls c = maybe False (isClassOrSubClass isFractionalClass)
                (tyConClass_maybe $ c)


isClassOrSubClass :: (Class -> Bool) -> Class -> Bool
isClassOrSubClass p cls
  = p cls || any (isClassOrSubClass p . fst)
                 (mapMaybe getClassPredTys_maybe (classSCTheta cls))

-- MOVE TO TYPES
instance TyConable Symbol where
  isFun   s = F.funConName == s
  isList  s = F.listConName == s
  isTuple s = F.tupConName == s
  ppTycon   = text . F.symbolString

instance TyConable F.LocSymbol where
  isFun   = isFun   . F.val
  isList  = isList  . F.val
  isTuple = isTuple . F.val
  ppTycon = ppTycon . F.val

instance TyConable BTyCon where
  isFun   = isFun . btc_tc
  isList  = isList . btc_tc
  isTuple = isTuple . btc_tc
  isClass = isClassBTyCon
  ppTycon = ppTycon . btc_tc


instance Eq RTyCon where
  x == y = rtc_tc x == rtc_tc y

instance Eq BTyCon where
  x == y = btc_tc x == btc_tc y

instance F.Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c

instance F.Fixpoint BTyCon where
  toFix = text . F.symbolString . F.val . btc_tc

instance F.Fixpoint Cinfo where
  toFix = text . showPpr . ci_loc

instance F.PPrint RTyCon where
  pprintTidy _ = text . showPpr . rtc_tc

instance F.PPrint BTyCon where
  pprintTidy _ = text . F.symbolString . F.val . btc_tc

instance F.PPrint v => F.PPrint (RTVar v s) where
  pprintTidy k (RTVar x _) = F.pprintTidy k x

instance Show RTyCon where
  show = F.showpp

instance Show BTyCon where
  show = F.showpp

--------------------------------------------------------------------------
-- | Refined Instances ---------------------------------------------------
--------------------------------------------------------------------------

data RInstance t = RI
  { riclass :: BTyCon
  , ritype  :: [t]
  , risigs  :: [(F.LocSymbol, RISig t)]
  } deriving (Generic, Functor, Data, Typeable, Show)

data RISig t = RIAssumed t | RISig t
  deriving (Generic, Functor, Data, Typeable, Show)

instance (B.Binary t) => B.Binary (RInstance t)
instance (B.Binary t) => B.Binary (RISig t)

newtype DEnv x ty = DEnv (M.HashMap x (M.HashMap Symbol (RISig ty)))
                    deriving (Monoid, Show)

type RDEnv = DEnv Var SpecType


--------------------------------------------------------------------------
-- | Values Related to Specifications ------------------------------------
--------------------------------------------------------------------------

data Axiom b s e = Axiom
  { aname  :: (Var, Maybe DataCon)
  , rname  :: Maybe b
  , abinds :: [b]
  , atypes :: [s]
  , alhs   :: e
  , arhs   :: e
  }

type HAxiom = Axiom Var    Type CoreExpr

type AxiomEq = F.Equation

-- data AxiomEq = AxiomEq
--   { axiomName :: Symbol             -- ^ name of function
--   , axiomArgs :: [(Symbol, F.Sort)] -- ^ parameters and sorts
--   , axiomBody :: Expr               -- ^ TODO:???
--   -- , axiomEq   :: Expr               -- ^ TODO:??? What is diff between body and eq?
--   , axiomSort :: F.Sort             -- ^ output sort
--   } deriving (Generic, Show)
-- instance B.Binary AxiomEq
-- instance F.PPrint AxiomEq where
--   pprintTidy k (AxiomEq n xs b _ _) = text "axeq" <+> F.pprint n <+> F.pprint xs <+> ":=" <+> F.pprintTidy k b

instance Show (Axiom Var Type CoreExpr) where
  show (Axiom (n, c) v bs _ts lhs rhs) = "Axiom : " ++
                                         "\nFun Name: " ++ (showPpr n) ++
                                         "\nReal Name: " ++ (showPpr v) ++
                                         "\nData Con: " ++ (showPpr c) ++
                                         "\nArguments:" ++ (showPpr bs)  ++
                                         -- "\nTypes    :" ++ (showPpr ts)  ++
                                         "\nLHS      :" ++ (showPpr lhs) ++
                                         "\nRHS      :" ++ (showPpr rhs)

{-

instance F.Subable AxiomEq where
  syms   a = F.syms (axiomBody a) ++ F.syms (axiomEq a)
  subst su = mapAxiomEqExpr (F.subst su)
  substf f = mapAxiomEqExpr (F.substf f)
  substa f = mapAxiomEqExpr (F.substa f)

mapAxiomEqExpr :: (Expr -> Expr) -> AxiomEq -> AxiomEq
mapAxiomEqExpr f a = a { axiomBody = f (axiomBody a)
                       , axiomEq   = f (axiomEq   a) }

-}
--------------------------------------------------------------------------------
-- | Data type refinements
--------------------------------------------------------------------------------
data DataDecl   = D
  { tycName   :: DataName              -- ^ Type  Constructor Name
  , tycTyVars :: [Symbol]              -- ^ Tyvar Parameters
  , tycPVars  :: [PVar BSort]          -- ^ PVar  Parameters
  , tycTyLabs :: [Symbol]              -- ^ PLabel  Parameters
  , tycDCons  :: [DataCtor]            -- ^ Data Constructors
  , tycSrcPos :: !F.SourcePos          -- ^ Source Position
  , tycSFun   :: Maybe SizeFun         -- ^ Default termination measure
  , tycPropTy :: Maybe BareType        -- ^ Type of Ind-Prop
  , tycKind   :: !DataDeclKind         -- ^ User-defined or Auto-lifted
  } deriving (Data, Typeable, Generic)

-- | The name of the `TyCon` corresponding to a `DataDecl`
data DataName
  = DnName !F.LocSymbol  -- ^ for 'isVanillyAlgTyCon' we can directly use the `TyCon` name
  | DnCon  !F.LocSymbol  -- ^ for 'FamInst' TyCon we save some `DataCon` name
  deriving (Eq, Ord, Data, Typeable, Generic)

-- | Data Constructor
data DataCtor = DataCtor
  { dcName   :: F.LocSymbol               -- ^ DataCon name
  , dcFields :: [(Symbol, BareType)]      -- ^ [(fieldName, fieldType)]
  , dcResult :: Maybe BareType            -- ^ Possible output (if in GADT form)
  } deriving (Data, Typeable, Generic)

-- | Termination expressions
data SizeFun
  = IdSizeFun              -- ^ \x -> F.EVar x
  | SymSizeFun F.LocSymbol -- ^ \x -> f x
  deriving (Data, Typeable, Generic)

-- | What kind of `DataDecl` is it?
data DataDeclKind
  = DataUser           -- ^ User defined data-definitions         (should have refined fields)
  | DataReflected      -- ^ Automatically lifted data-definitions (do not have refined fields)
  deriving (Eq, Data, Typeable, Generic, Show)

instance Show SizeFun where
  show IdSizeFun      = "IdSizeFun"
  show (SymSizeFun x) = "SymSizeFun " ++ show (F.val x)

szFun :: SizeFun -> Symbol -> Expr
szFun IdSizeFun      = F.EVar
szFun (SymSizeFun f) = \x -> F.mkEApp (F.symbol <$> f) [F.EVar x]

data HasDataDecl
  = NoDecl  (Maybe SizeFun)
  | HasDecl
  deriving (Show)

hasDecl :: DataDecl -> HasDataDecl
hasDecl d
  | null (tycDCons d)
  = NoDecl (tycSFun d)
  -- // | Just s <- tycSFun d, null (tycDCons d)
  -- // = NoDecl (Just s)
  | otherwise
  = HasDecl

instance Hashable DataName where
  hashWithSalt i = hashWithSalt i . F.symbol


instance NFData   SizeFun
instance B.Binary SizeFun
instance NFData   DataDeclKind
instance B.Binary DataDeclKind
instance B.Binary DataName
instance B.Binary DataCtor
instance B.Binary DataDecl

instance Eq DataDecl where
  d1 == d2 = tycName d1 == tycName d2

instance Ord DataDecl where
  compare d1 d2 = compare (tycName d1) (tycName d2)

instance F.Loc DataCtor where
  srcSpan = F.srcSpan . dcName

instance F.Loc DataDecl where
  srcSpan = srcSpanFSrcSpan . sourcePosSrcSpan . tycSrcPos

instance F.Loc DataName where
  srcSpan (DnName z) = F.srcSpan z
  srcSpan (DnCon  z) = F.srcSpan z


-- | For debugging.
instance Show DataDecl where
  show dd = printf "DataDecl: data = %s, tyvars = %s, sizeFun = %s, kind = %s" -- [at: %s]"
              (show $ tycName   dd)
              (show $ tycTyVars dd)
              (show $ tycSFun   dd)
              (show $ tycKind   dd)


instance Show DataName where
  show (DnName n) =               show (F.val n)
  show (DnCon  c) = "datacon:" ++ show (F.val c)

instance F.PPrint SizeFun where
  pprintTidy _ (IdSizeFun)    = "[id]"
  pprintTidy _ (SymSizeFun x) = brackets (F.pprint (F.val x))

instance F.Symbolic DataName where
  symbol = F.val . dataNameSymbol

instance F.Symbolic DataDecl where
  symbol = F.symbol . tycName

instance F.PPrint DataName where
  pprintTidy k (DnName n) = F.pprintTidy k (F.val n)
  pprintTidy k (DnCon  n) = F.pprintTidy k (F.val n)

  -- symbol (DnName z) = F.suffixSymbol "DnName" (F.val z)
  -- symbol (DnCon  z) = F.suffixSymbol "DnCon"  (F.val z)

dataNameSymbol :: DataName -> F.LocSymbol
dataNameSymbol (DnName z) = z
dataNameSymbol (DnCon  z) = z

--------------------------------------------------------------------------------
-- | Refinement Type Aliases
--------------------------------------------------------------------------------
data RTAlias x a = RTA
  { rtName  :: Symbol             -- ^ name of the alias
  , rtTArgs :: [x]                -- ^ type parameters
  , rtVArgs :: [x]                -- ^ value parameters
  , rtBody  :: a                  -- ^ what the alias expands to
  , rtPos   :: F.SourcePos          -- ^ start position
  , rtPosE  :: F.SourcePos          -- ^ end   position
  } deriving (Data, Typeable, Generic)

instance (B.Binary x, B.Binary a) => B.Binary (RTAlias x a)

mapRTAVars :: (a -> tv) -> RTAlias a ty -> RTAlias tv ty
mapRTAVars f rt = rt { rtTArgs = f <$> rtTArgs rt
                     , rtVArgs = f <$> rtVArgs rt
                     }

lmapEAlias :: LMap -> RTAlias Symbol Expr
lmapEAlias (LMap v ys e) = RTA (F.val v) [] ys e (F.loc v) (F.loc v)


--------------------------------------------------------------------------------
-- | Constructor and Destructors for RTypes ------------------------------------
--------------------------------------------------------------------------------

data RTypeRep c tv r = RTypeRep
  { ty_vars   :: [RTVar tv (RType c tv ())]
  , ty_preds  :: [PVar (RType c tv ())]
  , ty_labels :: [Symbol]
  , ty_binds  :: [Symbol]
  , ty_refts  :: [r]
  , ty_args   :: [RType c tv r]
  , ty_res    :: (RType c tv r)
  }

fromRTypeRep :: RTypeRep c tv r -> RType c tv r
fromRTypeRep (RTypeRep {..})
  = mkArrow ty_vars ty_preds ty_labels arrs ty_res
  where
    arrs = safeZip3WithError ("fromRTypeRep: " ++ show (length ty_binds, length ty_args, length ty_refts)) ty_binds ty_args ty_refts

toRTypeRep           :: RType c tv r -> RTypeRep c tv r
toRTypeRep t         = RTypeRep αs πs ls xs rs ts t''
  where
    (αs, πs, ls, t')  = bkUniv  t
    (xs, ts, rs, t'') = bkArrow t'

mkArrow :: [RTVar tv (RType c tv ())]
        -> [PVar (RType c tv ())]
        -> [Symbol]
        -> [(Symbol, RType c tv r, r)]
        -> RType c tv r
        -> RType c tv r
mkArrow αs πs ls xts = mkUnivs αs πs ls . mkArrs xts
  where
    mkArrs xts t  = foldr (\(b,t1,r) t2 -> RFun b t1 t2 r) t xts

bkArrowDeep :: RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
bkArrowDeep (RAllT _ t)     = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RAllS _ t)     = bkArrowDeep t
bkArrowDeep (RFun x t t' r) = let (xs, ts, rs, t'') = bkArrowDeep t'  in (x:xs, t:ts, r:rs, t'')
bkArrowDeep t               = ([], [], [], t)

bkArrow :: RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
bkArrow (RFun x t t' r) = let (xs, ts, rs, t'') = bkArrow t'  in (x:xs, t:ts, r:rs, t'')
bkArrow t               = ([], [], [], t)

safeBkArrow :: RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
safeBkArrow (RAllT _ _) = panic Nothing "safeBkArrow on RAllT"
safeBkArrow (RAllP _ _) = panic Nothing "safeBkArrow on RAllP"
safeBkArrow (RAllS _ t) = safeBkArrow t
safeBkArrow t           = bkArrow t

mkUnivs :: (Foldable t, Foldable t1, Foldable t2)
        => t  (RTVar tv (RType c tv ()))
        -> t1 (PVar (RType c tv ()))
        -> t2 Symbol
        -> RType c tv r
        -> RType c tv r
mkUnivs αs πs ls t = foldr RAllT (foldr RAllP (foldr RAllS t ls) πs) αs

bkUniv :: RType t1 a t2 -> ([RTVar a (RType t1 a ())], [PVar (RType t1 a ())], [Symbol], RType t1 a t2)
bkUniv (RAllT α t)      = let (αs, πs, ls, t') = bkUniv t in  (α:αs, πs, ls, t')
bkUniv (RAllP π t)      = let (αs, πs, ls, t') = bkUniv t in  (αs, π:πs, ls, t')
bkUniv (RAllS s t)      = let (αs, πs, ss, t') = bkUniv t in  (αs, πs, s:ss, t')
bkUniv t                = ([], [], [], t)

bkClass :: TyConable c
        => RType c tv r -> ([(c, [RType c tv r])], RType c tv r)
bkClass (RFun _ (RApp c t _ _) t' _)
  | isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RRTy e r o t)
  = let (cs, t') = bkClass t in (cs, RRTy e r o t')
bkClass t
  = ([], t)

rFun :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun b t t' = RFun b t t' mempty

rCls :: Monoid r => TyCon -> [RType RTyCon tv r] -> RType RTyCon tv r
rCls c ts   = RApp (RTyCon c [] defaultTyConInfo) ts [] mempty

rRCls :: Monoid r => c -> [RType c tv r] -> RType c tv r
rRCls rc ts = RApp rc ts [] mempty

addInvCond :: SpecType -> RReft -> SpecType
addInvCond t r'
  | F.isTauto $ ur_reft r' -- null rv
  = t
  | otherwise
  = fromRTypeRep $ trep {ty_res = RRTy [(x', tbd)] r OInv tbd}
  where
    trep = toRTypeRep t
    tbd  = ty_res trep
    r    = r' {ur_reft = F.Reft (v, rx)}
    su   = (v, F.EVar x')
    x'   = "xInv"
    rx   = F.PIff (F.EVar v) $ F.subst1 rv su
    F.Reft(v, rv) = ur_reft r'

-------------------------------------------

instance F.Subable Stratum where
  syms (SVar s) = [s]
  syms _        = []
  subst su (SVar s) = SVar $ F.subst su s
  subst _ s         = s
  substf f (SVar s) = SVar $ F.substf f s
  substf _ s        = s
  substa f (SVar s) = SVar $ F.substa f s
  substa _ s        = s

instance F.Reftable Strata where
  isTauto []         = True
  isTauto _          = False

  ppTy _             = panic Nothing "ppTy on Strata"
  toReft _           = mempty
  params s           = [l | SVar l <- s]
  bot _              = []
  top _              = []

  ofReft = todo Nothing "TODO: Strata.ofReft"


class F.Reftable r => UReftable r where
  ofUReft :: UReft F.Reft -> r
  ofUReft (MkUReft r _ _) = F.ofReft r


instance UReftable (UReft F.Reft) where
   ofUReft r = r

instance UReftable () where
   ofUReft _ = mempty

instance (F.PPrint r, F.Reftable r) => F.Reftable (UReft r) where
  isTauto                 = isTauto_ureft
  ppTy                    = ppTy_ureft
  toReft (MkUReft r ps _) = F.toReft r `F.meet` F.toReft ps
  params (MkUReft r _ _)  = F.params r
  bot (MkUReft r _ s)     = MkUReft (F.bot r) (Pr []) (F.bot s)
  top (MkUReft r p s)     = MkUReft (F.top r) (F.top p) s
  ofReft r                = MkUReft (F.ofReft r) mempty mempty

instance F.Expression (UReft ()) where
  expr = F.expr . F.toReft



isTauto_ureft :: F.Reftable r => UReft r -> Bool
isTauto_ureft u      = F.isTauto (ur_reft u) && F.isTauto (ur_pred u) -- && (isTauto $ ur_strata u)

ppTy_ureft :: F.Reftable r => UReft r -> Doc -> Doc
ppTy_ureft u@(MkUReft r p s) d
  | isTauto_ureft  u  = d
  | otherwise         = ppr_reft r (F.ppTy p d) s

ppr_reft :: (F.PPrint [t], F.Reftable r) => r -> Doc -> [t] -> Doc
ppr_reft r d s       = braces (F.pprint v <+> colon <+> d <> ppr_str s <+> text "|" <+> F.pprint r')
  where
    r'@(F.Reft (v, _)) = F.toReft r

ppr_str :: F.PPrint [t] => [t] -> Doc
ppr_str [] = empty
ppr_str s  = text "^" <> F.pprint s

instance F.Subable r => F.Subable (UReft r) where
  syms (MkUReft r p _)     = F.syms r ++ F.syms p
  subst s (MkUReft r z l)  = MkUReft (F.subst s r)  (F.subst s z)  (F.subst s l)
  substf f (MkUReft r z l) = MkUReft (F.substf f r) (F.substf f z) (F.substf f l)
  substa f (MkUReft r z l) = MkUReft (F.substa f r) (F.substa f z) (F.substa f l)

instance (F.Reftable r, TyConable c) => F.Subable (RTProp c tv r) where
  syms (RProp  ss r)     = (fst <$> ss) ++ F.syms r

  subst su (RProp ss (RHole r)) = RProp ss (RHole (F.subst su r))
  subst su (RProp  ss t) = RProp ss (F.subst su <$> t)

  substf f (RProp ss (RHole r)) = RProp ss (RHole (F.substf f r))
  substf f (RProp  ss t) = RProp ss (F.substf f <$> t)

  substa f (RProp ss (RHole r)) = RProp ss (RHole (F.substa f r))
  substa f (RProp  ss t) = RProp ss (F.substa f <$> t)


instance (F.Subable r, F.Reftable r, TyConable c) => F.Subable (RType c tv r) where
  syms        = foldReft (\_ r acc -> F.syms r ++ acc) []
  substa f    = emapExprArg (\_ -> F.substa f) []      . mapReft  (F.substa f)
  substf f    = emapExprArg (\_ -> F.substf f) []      . emapReft (F.substf . F.substfExcept f) []
  subst su    = emapExprArg (\_ -> F.subst su) []      . emapReft (F.subst  . F.substExcept su) []
  subst1 t su = emapExprArg (\_ e -> F.subst1 e su) [] $ emapReft (\xs r -> F.subst1Except xs r su) [] t


instance F.Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = panic Nothing "No BOT instance for Predicate"
  -- NV: This does not print abstract refinements....
  -- HACK: Hiding to not render types in WEB DEMO. NEED TO FIX.
  ppTy r d | F.isTauto r      = d
           | not (ppPs ppEnv) = d
           | otherwise        = d <> (angleBrackets $ F.pprint r)

  toReft (Pr ps@(p:_))        = F.Reft (parg p, F.pAnd $ pToRef <$> ps)
  toReft _                    = mempty
  params                      = todo Nothing "TODO: instance of params for Predicate"

  ofReft = todo Nothing "TODO: Predicate.ofReft"

pToRef :: PVar a -> F.Expr
pToRef p = pApp (pname p) $ (F.EVar $ parg p) : (thd3 <$> pargs p)

pApp      :: Symbol -> [Expr] -> Expr
pApp p es = F.mkEApp fn (F.EVar p:es)
  where
    fn    = F.dummyLoc (pappSym n)
    n     = length es

pappSym :: Show a => a -> Symbol
pappSym n  = F.symbol $ "papp" ++ show n

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

isTrivial :: (F.Reftable r, TyConable c) => RType c tv r -> Bool
isTrivial t = foldReft (\_ r b -> F.isTauto r && b) True t

mapReft ::  (r1 -> r2) -> RType c tv r1 -> RType c tv r2
mapReft f = emapReft (\_ -> f) []

emapReft ::  ([Symbol] -> r1 -> r2) -> [Symbol] -> RType c tv r1 -> RType c tv r2
emapReft f γ (RVar α r)          = RVar  α (f γ r)
emapReft f γ (RAllT α t)         = RAllT α (emapReft f γ t)
emapReft f γ (RAllP π t)         = RAllP π (emapReft f γ t)
emapReft f γ (RAllS p t)         = RAllS p (emapReft f γ t)
emapReft f γ (RFun x t t' r)     = RFun  x (emapReft f γ t) (emapReft f (x:γ) t') (f (x:γ) r)
emapReft f γ (RApp c ts rs r)    = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (RAllE z t t')      = RAllE z (emapReft f γ t) (emapReft f γ t')
emapReft f γ (REx z t t')        = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)        = RExprArg e
emapReft f γ (RAppTy t t' r)     = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft f γ (RRTy e r o t)      = RRTy  (mapSnd (emapReft f γ) <$> e) (f γ r) o (emapReft f γ t)
emapReft f γ (RHole r)           = RHole (f γ r)

emapRef :: ([Symbol] -> t -> s) ->  [Symbol] -> RTProp c tv t -> RTProp c tv s
emapRef  f γ (RProp s (RHole r))  = RProp s $ RHole (f γ r)
emapRef  f γ (RProp s t)         = RProp s $ emapReft f γ t

emapExprArg :: ([Symbol] -> Expr -> Expr) -> [Symbol] -> RType c tv r -> RType c tv r
emapExprArg f = go
  where
    go _ t@(RVar {})        = t
    go _ t@(RHole {})       = t
    go γ (RAllT α t)        = RAllT α (go γ t)
    go γ (RAllP π t)        = RAllP π (go γ t)
    go γ (RAllS p t)        = RAllS p (go γ t)
    go γ (RFun x t t' r)    = RFun  x (go γ t) (go (x:γ) t') r
    go γ (RApp c ts rs r)   = RApp  c (go γ <$> ts) (mo γ <$> rs) r
    go γ (RAllE z t t')     = RAllE z (go γ t) (go γ t')
    go γ (REx z t t')       = REx   z (go γ t) (go γ t')
    go γ (RExprArg e)       = RExprArg (f γ <$> F.tracepp "RExprArg" e)
    go γ (RAppTy t t' r)    = RAppTy (go γ t) (go γ t') r
    go γ (RRTy e r o t)     = RRTy  (mapSnd (go γ) <$> e) r o (go γ t)
    mo _ t@(RProp _ (RHole {})) = t
    mo γ (RProp s t)            = RProp s (go γ t)


foldRType :: (acc -> RType c tv r -> acc) -> acc -> RType c tv r -> acc
foldRType f = go
  where
    step a t                = go (f a t) t
    prep a (RProp _ (RHole {})) = a
    prep a (RProp _ t)      = step a t
    go a (RVar {})          = a
    go a (RHole {})         = a
    go a (RExprArg {})      = a
    go a (RAllT _ t)        = step a t
    go a (RAllP _ t)        = step a t
    go a (RAllS _ t)        = step a t
    go a (RFun _ t t' _)    = foldl' step a [t, t']
    go a (RAllE _ t t')     = foldl' step a [t, t']
    go a (REx _ t t')       = foldl' step a [t, t']
    go a (RAppTy t t' _)    = foldl' step a [t, t']
    go a (RApp _ ts rs _)   = foldl' prep (foldl' step a ts) rs
    go a (RRTy e _ _ t)     = foldl' step a (t : (snd <$> e))

------------------------------------------------------------------------------------------------------
-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t
-- same as GhcMisc isBaseType

-- isBase :: RType a -> Bool

-- set all types to basic types, haskell `tx -> t` is translated to Arrow tx t
-- isBase _ = True

isBase :: RType t t1 t2 -> Bool
isBase (RAllT _ t)      = isBase t
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RFun _ _ _ _)   = False
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase (RRTy _ _ _ t)   = isBase t
isBase (RAllE _ _ t)    = isBase t
isBase (REx _ _ t)      = isBase t
isBase _                = False

isFunTy :: RType t t1 t2 -> Bool
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

mapPropM :: (Monad m) => (RTProp c tv r -> m (RTProp c tv r)) -> RType c tv r -> m (RType c tv r)
mapPropM _ (RVar α r)         = return $ RVar  α r
mapPropM f (RAllT α t)        = liftM   (RAllT α)   (mapPropM f t)
mapPropM f (RAllP π t)        = liftM   (RAllP π)   (mapPropM f t)
mapPropM f (RAllS s t)        = liftM   (RAllS s)   (mapPropM f t)
mapPropM f (RFun x t t' r)    = liftM3  (RFun x)    (mapPropM f t)          (mapPropM f t') (return r)
mapPropM f (RApp c ts rs r)   = liftM3  (RApp  c)   (mapM (mapPropM f) ts)  (mapM f rs)     (return r)
mapPropM f (RAllE z t t')     = liftM2  (RAllE z)   (mapPropM f t)          (mapPropM f t')
mapPropM f (REx z t t')       = liftM2  (REx z)     (mapPropM f t)          (mapPropM f t')
mapPropM _ (RExprArg e)       = return  $ RExprArg e
mapPropM f (RAppTy t t' r)    = liftM3  RAppTy (mapPropM f t) (mapPropM f t') (return r)
mapPropM _ (RHole r)          = return $ RHole r
mapPropM f (RRTy xts r o t)   = liftM4  RRTy (mapM (mapSndM (mapPropM f)) xts) (return r) (return o) (mapPropM f t)


--------------------------------------------------------------------------------
-- foldReft :: (F.Reftable r, TyConable c) => (r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
-- foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) (\_ γ -> γ) emptyF.SEnv

--------------------------------------------------------------------------------
foldReft :: (F.Reftable r, TyConable c) => (F.SEnv (RType c tv r) -> r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft  f = foldReft' (\_ _ -> False) id (\γ _ -> f γ)

--------------------------------------------------------------------------------
foldReft' :: (F.Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> (RType c tv r -> b)
          -> (F.SEnv b -> Maybe (RType c tv r) -> r -> a -> a)
          -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft' logicBind g f = efoldReft logicBind
                            (\_ _ -> [])
                            (\_ -> [])
                            g
                            (\γ t r z -> f γ t r z)
                            (\_ γ -> γ)
                            F.emptySEnv



-- efoldReft :: F.Reftable r =>(p -> [RType c tv r] -> [(Symbol, a)])-> (RType c tv r -> a)-> (SEnv a -> Maybe (RType c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType c tv r-> c1
efoldReft :: (F.Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> (c  -> [RType c tv r] -> [(Symbol, a)])
          -> (RTVar tv (RType c tv ()) -> [(Symbol, a)])
          -> (RType c tv r -> a)
          -> (F.SEnv a -> Maybe (RType c tv r) -> r -> b -> b)
          -> (PVar (RType c tv ()) -> F.SEnv a -> F.SEnv a)
          -> F.SEnv a
          -> b
          -> RType c tv r
          -> b
efoldReft logicBind cb dty g f fp = go
  where
    -- folding over RType
    go γ z me@(RVar _ r)                = f γ (Just me) r z
    go γ z (RAllT a t)
       | ty_var_is_val a                = go (insertsSEnv γ (dty a)) z t
       | otherwise                      = go γ z t
    go γ z (RAllP p t)                  = go (fp p γ) z t
    go γ z (RAllS _ t)                  = go γ z t
    go γ z me@(RFun _ (RApp c ts _ _) t' r)
       | isClass c                      = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t')
    go γ z me@(RFun x t t' r)
       | logicBind x t                  = f γ (Just me) r (go γ' (go γ z t) t')
       | otherwise                      = f γ (Just me) r (go γ  (go γ z t) t')
       where
         γ'                             = insertSEnv x (g t) γ
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

mapBot :: (RType c tv r -> RType c tv r) -> RType c tv r -> RType c tv r
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

mapBotRef :: (RType c tv r -> RType c tv r)
          -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapBotRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapBotRef f (RProp s t)    = RProp  s $ mapBot f t

mapBind :: (Symbol -> Symbol) -> RType c tv r -> RType c tv r
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

mapBindRef :: (Symbol -> Symbol)
           -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapBindRef f (RProp s (RHole r)) = RProp (mapFst f <$> s) (RHole r)
mapBindRef f (RProp s t)         = RProp (mapFst f <$> s) $ mapBind f t


--------------------------------------------------
ofRSort ::  F.Reftable r => RType c tv () -> RType c tv r
ofRSort = fmap mempty

toRSort :: RType c tv r -> RType c tv ()
toRSort = stripAnnotations . mapBind (const F.dummySymbol) . fmap (const ())

stripAnnotations :: RType c tv r -> RType c tv r
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

stripAnnotationsRef :: Ref τ (RType c tv r) -> Ref τ (RType c tv r)
stripAnnotationsRef (RProp s (RHole r)) = RProp s (RHole r)
stripAnnotationsRef (RProp s t)         = RProp s $ stripAnnotations t

insertSEnv :: F.Symbol -> a -> F.SEnv a -> F.SEnv a
insertSEnv = F.insertSEnv

insertsSEnv :: F.SEnv a -> [(Symbol, a)] -> F.SEnv a
insertsSEnv  = foldr (\(x, t) γ -> insertSEnv x t γ)

rTypeValueVar :: (F.Reftable r) => RType c tv r -> Symbol
rTypeValueVar t = vv where F.Reft (vv,_) =  rTypeReft t

rTypeReft :: (F.Reftable r) => RType c tv r -> F.Reft
rTypeReft = fromMaybe F.trueReft . fmap F.toReft . stripRTypeBase

-- stripRTypeBase ::  RType a -> Maybe a
stripRTypeBase :: RType c tv r -> Maybe r
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

topRTypeBase :: (F.Reftable r) => RType c tv r -> RType c tv r
topRTypeBase = mapRBase F.top

mapRBase :: (r -> r) -> RType c tv r -> RType c tv r
mapRBase f (RApp c ts rs r) = RApp c ts rs $ f r
mapRBase f (RVar a r)       = RVar a $ f r
mapRBase f (RFun x t1 t2 r) = RFun x t1 t2 $ f r
mapRBase f (RAppTy t1 t2 r) = RAppTy t1 t2 $ f r
mapRBase _ t                = t


makeLType :: Stratum -> SpecType -> SpecType
makeLType l t = fromRTypeRep trep{ty_res = mapRBase f $ ty_res trep}
  where trep = toRTypeRep t
        f (MkUReft r p _) = MkUReft r p [l]


makeDivType :: SpecType -> SpecType
makeDivType = makeLType SDiv

makeFinType :: SpecType -> SpecType
makeFinType = makeLType SFin

getStrata :: RType t t1 (UReft r) -> [Stratum]
getStrata = maybe [] ur_strata . stripRTypeBase

-----------------------------------------------------------------------------
-- | F.PPrint -----------------------------------------------------------------
-----------------------------------------------------------------------------

instance Show Stratum where
  show SFin = "Fin"
  show SDiv = "Div"
  show SWhnf = "Whnf"
  show (SVar s) = show s

instance F.PPrint Stratum where
  pprintTidy _ = text . show

instance {-# OVERLAPPING #-} F.PPrint Strata where
  pprintTidy _ [] = empty
  pprintTidy k ss = hsep (F.pprintTidy k <$> nub ss)

instance F.PPrint (PVar a) where
  pprintTidy _ = ppr_pvar

ppr_pvar :: PVar a -> Doc
ppr_pvar (PV s _ _ xts) = F.pprint s <+> hsep (F.pprint <$> dargs xts)
  where
    dargs               = map thd3 . takeWhile (\(_, x, y) -> F.EVar x /= y)


instance F.PPrint Predicate where
  pprintTidy _ (Pr [])  = text "True"
  pprintTidy k (Pr pvs) = hsep $ punctuate (text "&") (F.pprintTidy k <$> pvs)


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

--------------------------------------------------------------------------------
-- | Error Data Type -----------------------------------------------------------
--------------------------------------------------------------------------------

type ErrorResult    = F.FixResult UserError
type Error          = TError SpecType


instance NFData a => NFData (TError a)

--------------------------------------------------------------------------------
-- | Source Information Associated With Constraints ----------------------------
--------------------------------------------------------------------------------

data Cinfo    = Ci { ci_loc :: !SrcSpan
                   , ci_err :: !(Maybe Error)
                   , ci_var :: !(Maybe Var)
                   }
                deriving (Eq, Ord, Generic)

instance F.Loc Cinfo where
  srcSpan = srcSpanFSrcSpan . ci_loc

instance NFData Cinfo

--------------------------------------------------------------------------------
-- | Module Names --------------------------------------------------------------
--------------------------------------------------------------------------------

data ModName = ModName !ModType !ModuleName deriving (Eq, Ord, Show)

instance F.PPrint ModName where
  pprintTidy _ = text . show

instance Show ModuleName where
  show = moduleNameString

instance F.Symbolic ModName where
  symbol (ModName _ m) = F.symbol m

instance F.Symbolic ModuleName where
  symbol = F.symbol . moduleNameFS

data ModType = Target | SrcImport | SpecImport deriving (Eq,Ord,Show)

isSrcImport :: ModName -> Bool
isSrcImport (ModName SrcImport _) = True
isSrcImport _                     = False

isSpecImport :: ModName -> Bool
isSpecImport (ModName SpecImport _) = True
isSpecImport _                      = False

getModName :: ModName -> ModuleName
getModName (ModName _ m) = m

getModString :: ModName -> String
getModString = moduleNameString . getModName


--------------------------------------------------------------------------------
-- | Refinement Type Aliases ---------------------------------------------------
--------------------------------------------------------------------------------
data RTEnv = RTE
  { typeAliases :: M.HashMap Symbol (RTAlias RTyVar SpecType)
  , exprAliases :: M.HashMap Symbol (RTAlias Symbol Expr)
  }

instance Monoid RTEnv where
  mempty                          = RTE M.empty M.empty
  (RTE x y) `mappend` (RTE x' y') = RTE (x `M.union` x') (y `M.union` y')

mapRT :: (M.HashMap Symbol (RTAlias RTyVar SpecType)
       -> M.HashMap Symbol (RTAlias RTyVar SpecType))
       -> RTEnv -> RTEnv
mapRT f e = e { typeAliases = f $ typeAliases e }

mapRE :: (M.HashMap Symbol (RTAlias Symbol Expr)
       -> M.HashMap Symbol (RTAlias Symbol Expr))
      -> RTEnv -> RTEnv
mapRE f e = e { exprAliases = f $ exprAliases e }


--------------------------------------------------------------------------------
-- | Measures
--------------------------------------------------------------------------------
data Body
  = E Expr          -- ^ Measure Refinement: {v | v = e }
  | P Expr          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Expr   -- ^ Measure Refinement: {v | p}
  deriving (Show, Data, Typeable, Generic, Eq)

data Def ty ctor = Def
  { measure :: F.LocSymbol
  , dparams :: [(Symbol, ty)]          -- measure parameters
  , ctor    :: ctor
  , dsort   :: Maybe ty
  , binds   :: [(Symbol, Maybe ty)]    -- measure binders: the ADT argument fields
  , body    :: Body
  } deriving (Show, Data, Typeable, Generic, Eq, Functor)

data Measure ty ctor = M
  { name :: F.LocSymbol
  , sort :: ty
  , eqns :: [Def ty ctor]
  } deriving (Data, Typeable, Generic, Functor)

instance Bifunctor Def where
  first f (Def m ps c s bs b) =
    Def m (map (second f) ps) c (fmap f s) (map (second (fmap f)) bs) b
  second f (Def m ps c s bs b) =
    Def m ps (f c) s bs b

instance Bifunctor Measure where
  first f (M n s es) =
    M n (f s) (map (first f) es)
  second f (M n s es) =
    M n s (map (second f) es)

instance                             B.Binary Body
instance (B.Binary t, B.Binary c) => B.Binary (Def     t c)
instance (B.Binary t, B.Binary c) => B.Binary (Measure t c)

-- NOTE: don't use the TH versions since they seem to cause issues
-- building on windows :(
-- deriveBifunctor ''Def
-- deriveBifunctor ''Measure

data CMeasure ty = CM
  { cName :: F.LocSymbol
  , cSort :: ty
  } deriving (Data, Typeable, Generic, Functor)

instance F.PPrint Body where
  pprintTidy k (E e)   = F.pprintTidy k e
  pprintTidy k (P p)   = F.pprintTidy k p
  pprintTidy k (R v p) = braces (F.pprintTidy k v <+> "|" <+> F.pprintTidy k p)

instance F.PPrint a => F.PPrint (Def t a) where
  pprintTidy k (Def m p c _ bs body)
           = F.pprintTidy k m <+> F.pprintTidy k (fst <$> p) <+> cbsd <+> "=" <+> F.pprintTidy k body
    where
      cbsd = parens (F.pprintTidy k c <> hsep (F.pprintTidy k `fmap` (fst <$> bs)))

instance (F.PPrint t, F.PPrint a) => F.PPrint (Measure t a) where
  pprintTidy k (M n s eqs) =  F.pprintTidy k n <+> {- parens (pprintTidy k (loc n)) <+> -} "::" <+> F.pprintTidy k s
                              $$ vcat (F.pprintTidy k `fmap` eqs)


instance F.PPrint (Measure t a) => Show (Measure t a) where
  show = F.showpp

instance F.PPrint t => F.PPrint (CMeasure t) where
  pprintTidy k (CM n s) =  F.pprintTidy k n <+> "::" <+> F.pprintTidy k s

instance F.PPrint (CMeasure t) => Show (CMeasure t) where
  show = F.showpp


instance F.Subable (Measure ty ctor) where
  syms (M _ _ es)      = concatMap F.syms es
  substa f  (M n s es) = M n s $ F.substa f  <$> es
  substf f  (M n s es) = M n s $ F.substf f  <$> es
  subst  su (M n s es) = M n s $ F.subst  su <$> es

instance F.Subable (Def ty ctor) where
  syms (Def _ sp _ _ sb bd)  = (fst <$> sp) ++ (fst <$> sb) ++ F.syms bd
  substa f  (Def m p c t b bd) = Def m p c t b $ F.substa f  bd
  substf f  (Def m p c t b bd) = Def m p c t b $ F.substf f  bd
  subst  su (Def m p c t b bd) = Def m p c t b $ F.subst  su bd

instance F.Subable Body where
  syms (E e)       = F.syms e
  syms (P e)       = F.syms e
  syms (R s e)     = s : F.syms e

  substa f (E e)   = E   (F.substa f e)
  substa f (P e)   = P   (F.substa f e)
  substa f (R s e) = R s (F.substa f e)

  substf f (E e)   = E   (F.substf f e)
  substf f (P e)   = P   (F.substf f e)
  substf f (R s e) = R s (F.substf f e)

  subst su (E e)   = E   (F.subst su e)
  subst su (P e)   = P   (F.subst su e)
  subst su (R s e) = R s (F.subst su e)

instance F.Subable t => F.Subable (WithModel t) where
  syms (NoModel t)     = F.syms t
  syms (WithModel _ t) = F.syms t
  substa f             = fmap (F.substa f)
  substf f             = fmap (F.substf f)
  subst su             = fmap (F.subst su)

data RClass ty = RClass
  { rcName    :: BTyCon
  , rcSupers  :: [ty]
  , rcTyVars  :: [BTyVar]
  , rcMethods :: [(F.LocSymbol, ty)]
  } deriving (Show, Functor, Data, Typeable, Generic)



instance B.Binary ty => B.Binary (RClass ty)


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
  -- , o_errors :: ![UserError]
  , o_types  :: !(AnnInfo a)
  , o_templs :: !(AnnInfo a)
  , o_bots   :: ![SrcSpan]
  , o_result :: ErrorResult
  } deriving (Typeable, Generic, Functor)

emptyOutput :: Output a
emptyOutput = O Nothing {- [] -} mempty mempty [] mempty

instance Monoid (Output a) where
  mempty        = emptyOutput
  mappend o1 o2 = O { o_vars   = sortNub <$> mappend (o_vars   o1) (o_vars   o2)
                    -- , o_errors = sortNub  $  mappend (o_errors o1) (o_errors o2)
                    , o_types  =             mappend (o_types  o1) (o_types  o2)
                    , o_templs =             mappend (o_templs o1) (o_templs o2)
                    , o_bots   = sortNub  $  mappend (o_bots o1)   (o_bots   o2)
                    , o_result =             mappend (o_result o1) (o_result o2)
                    }

--------------------------------------------------------------------------------
-- | KVar Profile --------------------------------------------------------------
--------------------------------------------------------------------------------

data KVKind
  = RecBindE    Var -- ^ Recursive binder      @letrec x = ...@
  | NonRecBindE Var -- ^ Non recursive binder  @let x = ...@
  | TypeInstE
  | PredInstE
  | LamE
  | CaseE       Int -- ^ Int is the number of cases
  | LetE
  | ProjectE        -- ^ Projecting out field of
  deriving (Generic, Eq, Ord, Show, Data, Typeable)

instance Hashable KVKind

newtype KVProf = KVP (M.HashMap KVKind Int) deriving (Generic)

emptyKVProf :: KVProf
emptyKVProf = KVP M.empty

updKVProf :: KVKind -> F.Kuts -> KVProf -> KVProf
updKVProf k kvs (KVP m) = KVP $ M.insert k (kn + n) m
  where
    kn                  = M.lookupDefault 0 k m
    n                   = S.size (F.ksVars kvs)

instance NFData KVKind

instance F.PPrint KVKind where
  pprintTidy _ = text . show

instance F.PPrint KVProf where
  pprintTidy k (KVP m) = F.pprintTidy k (M.toList m)

instance NFData KVProf

hole :: Expr
hole = F.PKVar "HOLE" mempty

isHole :: Expr -> Bool
isHole (F.PKVar ("HOLE") _) = True
isHole _                    = False

hasHole :: F.Reftable r => r -> Bool
hasHole = any isHole . F.conjuncts . F.reftPred . F.toReft

-- classToRApp :: SpecType -> SpecType
-- classToRApp (RCls cl ts)
--   = RApp (RTyCon (classTyCon cl) def def) ts mempty mempty

instance F.Symbolic DataCon where
  symbol = F.symbol . dataConWorkId

instance F.PPrint DataCon where
  pprintTidy _ = text . showPpr

instance Show DataCon where
  show = F.showpp


liquidBegin :: String
liquidBegin = ['{', '-', '@']

liquidEnd :: String
liquidEnd = ['@', '-', '}']

data MSpec ty ctor = MSpec
  { ctorMap  :: M.HashMap Symbol [Def ty ctor]
  , measMap  :: M.HashMap F.LocSymbol (Measure ty ctor)
  , cmeasMap :: M.HashMap F.LocSymbol (Measure ty ())
  , imeas    :: ![Measure ty ctor]
  } deriving (Data, Typeable, Generic, Functor)

instance Bifunctor MSpec   where
  first f (MSpec c m cm im) = MSpec (fmap (fmap (first f)) c)
                                    (fmap (first f) m)
                                    (fmap (first f) cm)
                                    (fmap (first f) im)
  second                    = fmap

instance (F.PPrint t, F.PPrint a) => F.PPrint (MSpec t a) where
  pprintTidy k =  vcat . fmap (F.pprintTidy k) . fmap snd . M.toList . measMap

instance (Show ty, Show ctor, F.PPrint ctor, F.PPrint ty) => Show (MSpec ty ctor) where
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
    | (k1, k2) : _ <- dups
      -- = panic Nothing $ err (head dups)
    = uError $ err k1 k2
    | otherwise
    = MSpec (M.unionWith (++) c1 c2) (m1 `M.union` m2) (cm1 `M.union` cm2) (im1 ++ im2)
    where
      dups = [(k1, k2) | k1 <- M.keys m1 , k2 <- M.keys m2, F.val k1 == F.val k2]
      err k1 k2 = ErrDupMeas (fSrcSpan k1) (F.pprint (F.val k1)) (fSrcSpan <$> [k1, k2])




--------------------------------------------------------------------------------
-- Nasty PP stuff
--------------------------------------------------------------------------------

instance F.PPrint BTyVar where
  pprintTidy _ (BTV α) = text (F.symbolString α)

instance F.PPrint RTyVar where
  pprintTidy _ (RTV α)
   | ppTyVar ppEnv  = ppr_tyvar α
   | otherwise      = ppr_tyvar_short α
   where
     ppr_tyvar :: Var -> Doc
     ppr_tyvar       = text . tvId

     ppr_tyvar_short :: TyVar -> Doc
     ppr_tyvar_short = text . showPpr

instance (F.PPrint r, F.Reftable r, F.PPrint t, F.PPrint (RType c tv r)) => F.PPrint (Ref t (RType c tv r)) where
  pprintTidy k (RProp ss s) = ppRefArgs k (fst <$> ss) <+> F.pprintTidy k s

ppRefArgs :: F.Tidy -> [Symbol] -> Doc
ppRefArgs _ [] = empty
ppRefArgs k ss = text "\\" <> hsep (ppRefSym k <$> ss ++ [F.vv Nothing]) <+> "->"

ppRefSym :: (Eq a, IsString a, F.PPrint a) => F.Tidy -> a -> Doc
ppRefSym _ "" = text "_"
ppRefSym k s  = F.pprintTidy k s
