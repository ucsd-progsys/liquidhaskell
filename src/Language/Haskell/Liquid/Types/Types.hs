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
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}

-- | This module should contain all the global type definitions and basic instances.

module Language.Haskell.Liquid.Types.Types (

  -- * Options
    module Language.Haskell.Liquid.UX.Config

  -- * Ghc Information
  , TargetVars   (..)
  , TyConMap     (..)

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
  , mkBTyCon
  -- , mkClassBTyCon, mkPromotedBTyCon
  , isClassBTyCon
  , BTyVar(..)

  -- * Refined Type Constructors
  , RTyCon (RTyCon, rtc_tc, rtc_info)
  , TyConInfo(..), defaultTyConInfo
  , rTyConPVs
  , rTyConPropVs
  -- , isClassRTyCon
  , isClassType, isEqType, isRVar, isBool, isEmbeddedClass

  -- * Refinement Types
  , RType (..), Ref(..), RTProp, rPropP
  , RTyVar (..)
  , RTAlias (..)
  , OkRT
  , lmapEAlias
  , dropImplicits

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
  , setRtvPol

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
  , SpecType, SpecProp, SpecRTVar
  , SpecRep
  , LocBareType, LocSpecType
  , RSort
  , UsedPVar, RPVar, RReft
  , REnv
  , AREnv (..)

  -- * Constructing & Destructing RTypes
  , RTypeRep(..), fromRTypeRep, toRTypeRep
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow
  , mkUnivs, bkUniv, bkClass, bkUnivClass, bkUnivClass'
  , rImpF, rFun, rFun', rCls, rRCls, rFunDebug

  -- * Manipulating `Predicates`
  , pvars, pappSym, pApp

  -- * Some tests on RTypes
  , isBase
  , isFunTy
  , isTrivial
  , hasHole 

  -- * Traversing `RType`
  , efoldReft, foldReft, foldReft'
  , emapReft, mapReft, mapReftM, mapPropM
  , mapExprReft
  , mapBot, mapBind, mapRFInfo
  , foldRType


  -- * ???
  , Oblig(..)
  , ignoreOblig
  , addInvCond

  -- * Inferred Annotations
  , AnnInfo (..)
  , Annot (..)

  -- * Hole Information 
  , HoleInfo(..)

  -- * Overall Output
  , Output (..)

  -- * Refinement Hole
  , hole, isHole, hasHoleTy

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
  , isSrcImport, isSpecImport, isTarget
  , getModName, getModString, qualifyModName

  -- * Refinement Type Aliases
  , RTEnv (..), BareRTEnv, SpecRTEnv, BareRTAlias, SpecRTAlias
  -- , mapRT, mapRE

  -- * Diagnostics, Warnings, Errors and Error Messages
  , module Language.Haskell.Liquid.Types.Errors
  , Error
  , ErrorResult
  , Warning
  , mkWarning
  , Diagnostics
  , mkDiagnostics
  , emptyDiagnostics
  , noErrors
  , allWarnings
  , allErrors
  , printWarning

  -- * Source information (associated with constraints)
  , Cinfo (..)

  -- * Measures
  , Measure (..)
  , UnSortedExprs, UnSortedExpr
  , MeasureKind (..)
  , CMeasure (..)
  , Def (..)
  , Body (..)
  , MSpec (..)
  
  -- * Scoping Info
  , BScope

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

  -- * CoreToLogic
  , LogicMap(..), toLogicMap, eAppWithMap, LMap(..)

  -- * Refined Instances
  , RDEnv, DEnv(..), RInstance(..), RISig(..), RILaws(..)
  , MethodType(..), getMethodType

  -- * Ureftable Instances
  , UReftable(..)

  -- * String Literals
  , liquidBegin, liquidEnd

  , Axiom(..), HAxiom

  -- , rtyVarUniqueSymbol, tyVarUniqueSymbol
  , rtyVarType, tyVarVar

  -- * Refined Function Info 
  , RFInfo(..), defRFInfo, mkRFInfo, classRFInfo, classRFInfoType

  , ordSrcSpan
  )
  where

import           Language.Haskell.Liquid.GHC.API as Ghc hiding ( Expr
                                                               , Target
                                                               , isFunTy
                                                               , LM
                                                               , ($+$)
                                                               , nest
                                                               , text
                                                               , blankLine
                                                               , (<+>)
                                                               , vcat
                                                               , hsep
                                                               , comma
                                                               , colon
                                                               , parens
                                                               , empty
                                                               , char
                                                               , panic
                                                               , int
                                                               , hcat
                                                               , showPpr
                                                               , punctuate
                                                               , mapSndM
                                                               , ($$)
                                                               , braces
                                                               , angleBrackets
                                                               , brackets
                                                               )
import           Data.String
import           GHC.Generics
import           Prelude                          hiding  (error)
import qualified Prelude

import           Control.Monad                          (liftM, liftM2, liftM3, liftM4)
import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Typeable                          (Typeable)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import qualified Data.Foldable                          as F
import           Data.Hashable
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import qualified Data.List                              as L
import           Data.Maybe                             (fromMaybe, mapMaybe)
import           Data.Function                          (on)
import           Data.List                              as L (foldl', nub, null)
import           Data.Text                              (Text)
import           Text.PrettyPrint.HughesPJ              hiding (first, (<>)) 
import           Text.Printf
import           Language.Fixpoint.Misc

import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.Types.Generics
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.GHC.Logging as GHC
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.UX.Config
import           Data.Default


-----------------------------------------------------------------------------
-- | Information about scope Binders Scope in
-----------------------------------------------------------------------------
{- In types with base refinement, e.g., {out:T {inner:a | ri} | ro }
If BScope = True , then the outer binder out is     in scope on ri
If BScope = False, then the outer binder out is not in scope on ri
-}

type BScope = Bool    
-----------------------------------------------------------------------------
-- | Information about Type Constructors
-----------------------------------------------------------------------------
data TyConMap = TyConMap 
  { tcmTyRTy    :: M.HashMap TyCon             RTyCon  -- ^ Map from GHC TyCon to RTyCon 
  , tcmFIRTy    :: M.HashMap (TyCon, [F.Sort]) RTyCon  -- ^ Map from GHC Family-Instances to RTyCon
  , tcmFtcArity :: M.HashMap TyCon             Int     -- ^ Arity of each Family-Tycon 
  }
 

data RFInfo = RFInfo {permitTC :: Maybe Bool }
  deriving (Generic, Data, Typeable, Show, Eq)

defRFInfo :: RFInfo
defRFInfo = RFInfo Nothing 

classRFInfo :: Bool -> RFInfo
classRFInfo b = RFInfo (Just b) 

classRFInfoType :: Bool -> RType c tv r -> RType c tv r
classRFInfoType b = fromRTypeRep .
                    (\trep@RTypeRep{..} -> trep{ty_info = map (\i -> i{permitTC = pure b}) ty_info}) .
                    toRTypeRep

mkRFInfo :: Config  -> RFInfo
mkRFInfo cfg = RFInfo $ Just (typeclass cfg)  

instance Hashable RFInfo
instance NFData RFInfo
instance B.Binary RFInfo

-----------------------------------------------------------------------------
-- | Printer ----------------------------------------------------------------
-----------------------------------------------------------------------------

data PPEnv = PP 
  { ppPs    :: Bool -- ^ print abstract-predicates 
  , ppTyVar :: Bool -- ^ print the unique suffix for each tyvar
  , ppShort :: Bool -- ^ print the tycons without qualification 
  , ppDebug :: Bool -- ^ gross with full info
  }
  deriving (Show)

ppEnv :: PPEnv
ppEnv = ppEnvDef 
          { ppPs    = True }   
          { ppDebug = True }   -- RJ: needed for resolution, because pp is used for serialization?

{- | [NOTE:ppEnv] For some mysterious reason, `ppDebug` must equal `True`
     or various tests fail e.g. tests/classes/pos/TypeEquality0{0,1}.hs
     Yikes. Find out why!
 -}

ppEnvDef :: PPEnv
ppEnvDef = PP False False False False

ppEnvShort :: PPEnv -> PPEnv
ppEnvShort pp = pp { ppShort = True }

------------------------------------------------------------------
-- Huh?
------------------------------------------------------------------
type Expr      = F.Expr
type Symbol    = F.Symbol


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
  mempty  = LM M.empty M.empty
  mappend = (<>)

instance Semigroup LogicMap where
  LM x1 x2 <> LM y1 y2 = LM (M.union x1 y1) (M.union x2 y2)

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
  { tcpLoc          :: !F.SourcePos
  , tcpCon          :: !TyCon
  , tcpFreeTyVarsTy :: ![RTyVar]
  , tcpFreePredTy   :: ![PVar RSort]
  , tcpVarianceTs   :: !VarianceInfo
  , tcpVariancePs   :: !VarianceInfo
  , tcpSizeFun      :: !(Maybe SizeFun)
  } deriving (Generic, Data, Typeable)

instance F.Loc TyConP where
  srcSpan tc = F.SS (tcpLoc tc) (tcpLoc tc)


-- TODO: just use Located instead of dc_loc, dc_locE
data DataConP = DataConP
  { dcpLoc        :: !F.SourcePos
  , dcpCon        :: !DataCon                -- ^ Corresponding GHC DataCon 
  , dcpFreeTyVars :: ![RTyVar]               -- ^ Type parameters
  , dcpFreePred   :: ![PVar RSort]           -- ^ Abstract Refinement parameters
  , dcpTyConstrs  :: ![SpecType]             -- ^ ? Class constraints (via `dataConStupidTheta`)
  , dcpTyArgs     :: ![(Symbol, SpecType)]   -- ^ Value parameters
  , dcpTyRes      :: !SpecType               -- ^ Result type
  , dcpIsGadt     :: !Bool                   -- ^ Was this specified in GADT style (if so, DONT use function names as fields)
  , dcpModule     :: !F.Symbol               -- ^ Which module was this defined in
  , dcpLocE       :: !F.SourcePos
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
  srcSpan d = F.SS (dcpLoc d) (dcpLocE d)

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

newtype Predicate  = Pr [UsedPVar] 
  deriving (Generic, Data, Typeable)
  deriving Hashable via Generically Predicate

instance Eq Predicate where
  (Pr vs) == (Pr ws)
      = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
        where
          vs' = L.sort vs
          ws' = L.sort ws



instance B.Binary Predicate

instance NFData Predicate where
  rnf _ = ()

instance Monoid Predicate where
  mempty  = pdTrue
  mappend = (<>)

instance Semigroup Predicate where
  p <> p' = pdAnd [p, p']

instance Semigroup a => Semigroup (UReft a) where
  MkUReft x y <> MkUReft x' y' = MkUReft (x <> x') (y <> y')

instance (Monoid a) => Monoid (UReft a) where
  mempty  = MkUReft mempty mempty
  mappend = (<>)


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
  symbol (RTV tv) = F.symbol tv -- tyVarUniqueSymbol tv

-- instance F.Symbolic RTyVar where
  -- symbol (RTV tv) = F.symbol . getName $ tv
-- rtyVarUniqueSymbol  :: RTyVar -> Symbol
-- rtyVarUniqueSymbol (RTV tv) = tyVarUniqueSymbol tv
-- tyVarUniqueSymbol :: TyVar -> Symbol
-- tyVarUniqueSymbol tv = F.symbol $ show (getName tv) ++ "_" ++ show (varUnique tv)

data BTyCon = BTyCon
  { btc_tc    :: !F.LocSymbol    -- ^ TyCon name with location information
  , btc_class :: !Bool           -- ^ Is this a class type constructor?
  , btc_prom  :: !Bool           -- ^ Is Promoted Data Con?
  }
  deriving (Generic, Data, Typeable)
  deriving Hashable via Generically BTyCon

instance B.Binary BTyCon

data RTyCon = RTyCon
  { rtc_tc    :: TyCon         -- ^ GHC Type Constructor
  , rtc_pvars :: ![RPVar]      -- ^ Predicate Parameters
  , rtc_info  :: !TyConInfo    -- ^ TyConInfo
  }
  deriving (Generic, Data, Typeable)

instance F.Symbolic RTyCon where
  symbol = F.symbol . rtc_tc 

instance F.Symbolic BTyCon where
  symbol = F.val . btc_tc

instance NFData BTyCon

instance NFData RTyCon

rtyVarType :: RTyVar -> Type
rtyVarType (RTV v) = TyVarTy v

tyVarVar :: RTVar RTyVar c -> Var
tyVarVar (RTVar (RTV v) _) = v



mkBTyCon :: F.LocSymbol -> BTyCon
mkBTyCon x = BTyCon x False False


-- | Accessors for @RTyCon@

isBool :: RType RTyCon t t1 -> Bool
isBool (RApp (RTyCon{rtc_tc = c}) _ _ _) = c == boolTyCon
isBool _                                 = False

isRVar :: RType c tv r -> Bool
isRVar (RVar _ _) = True
isRVar _          = False

isClassBTyCon :: BTyCon -> Bool
isClassBTyCon = btc_class

-- isClassRTyCon :: RTyCon -> Bool
-- isClassRTyCon x = (isClassTyCon $ rtc_tc x) || (rtc_tc x == eqPrimTyCon)

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

isEmbeddedClass :: TyConable c => RType c t t1 -> Bool
isEmbeddedClass (RApp c _ _ _) = isEmbeddedDict c
isEmbeddedClass _              = False

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

--------------------------------------------------------------------------------
-- | Unified Representation of Refinement Types --------------------------------
--------------------------------------------------------------------------------

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
    , rt_rinfo  :: !RFInfo
    , rt_in     :: !(RType c tv r)
    , rt_out    :: !(RType c tv r)
    , rt_reft   :: !r
    }

  | RImpF  {
      rt_bind   :: !Symbol
    , rt_rinfo  :: !RFInfo -- NNV TODO merge with RFun
    , rt_in     :: !(RType c tv r)
    , rt_out    :: !(RType c tv r)
    , rt_reft   :: !r
    }

  | RAllT {
      rt_tvbind :: !(RTVU c tv) -- RTVar tv (RType c tv ()))
    , rt_ty     :: !(RType c tv r)
    , rt_ref    :: !r
    }

  -- | "forall x y <z :: Nat, w :: Int> . TYPE"
  --               ^^^^^^^^^^^^^^^^^^^ (rt_pvbind)
  | RAllP {
      rt_pvbind :: !(PVU c tv) 
    , rt_ty     :: !(RType c tv r)
    }

  -- | For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
  --   * the `RProp`  denoted by `{\h -> v > h}` to
  --   * the `RTyCon` denoted by `[]`.
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
  deriving (Eq, Generic, Data, Typeable, Functor)
  deriving Hashable via Generically (RType c tv r)

instance (B.Binary c, B.Binary tv, B.Binary r) => B.Binary (RType c tv r)
instance (NFData c, NFData tv, NFData r)       => NFData (RType c tv r)

ignoreOblig :: RType t t1 t2 -> RType t t1 t2
ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t

dropImplicits :: RType c tv r -> RType c tv r
dropImplicits (RImpF _ _ _ o _) = dropImplicits o
dropImplicits (RFun x ii i o r) = RFun x ii (dropImplicits i) (dropImplicits o) r
dropImplicits (RAllP p t) = RAllP p (dropImplicits t)
dropImplicits (RAllT p t r) = RAllT p (dropImplicits t) r
dropImplicits (RApp c as ps r) = RApp c (dropImplicits <$> as) (dropImplicitsRP <$> ps) r
dropImplicits (RAllE p t t') = RAllE p (dropImplicits t) (dropImplicits t')
dropImplicits (REx s t t')   = REx   s (dropImplicits t) (dropImplicits t')
dropImplicits (RAppTy t t' r)   = RAppTy (dropImplicits t) (dropImplicits t') r
dropImplicits (RRTy e r o t) = RRTy (second dropImplicits <$> e) r o (dropImplicits t)
dropImplicits t = t

dropImplicitsRP :: RTProp c tv r -> RTProp c tv r
dropImplicitsRP (RProp as b) = RProp (second dropImplicits <$> as) (dropImplicits b)


makeRTVar :: tv -> RTVar tv s
makeRTVar a = RTVar a (RTVNoInfo True)

instance (Eq tv) => Eq (RTVar tv s) where
  t1 == t2 = (ty_var_value t1) == (ty_var_value t2)

data RTVar tv s = RTVar
  { ty_var_value :: tv
  , ty_var_info  :: RTVInfo s
  } deriving (Generic, Data, Typeable)
    deriving Hashable via Generically (RTVar tv s)

mapTyVarValue :: (tv1 -> tv2) -> RTVar tv1 s -> RTVar tv2 s
mapTyVarValue f v = v {ty_var_value = f $ ty_var_value v}

dropTyVarInfo :: RTVar tv s1 -> RTVar tv s2
dropTyVarInfo v = v{ty_var_info = RTVNoInfo True }

data RTVInfo s
  = RTVNoInfo { rtv_is_pol :: Bool }
  | RTVInfo { rtv_name   :: Symbol
            , rtv_kind   :: s
            , rtv_is_val :: Bool
            , rtv_is_pol :: Bool -- true iff the type variable gets instantiated with 
                                 -- any refinement (ie is polymorphic on refinements), 
                                 -- false iff instantiation is with true refinement 
            } deriving (Generic, Data, Typeable, Functor)
              deriving Hashable via Generically (RTVInfo s)


setRtvPol :: RTVar tv a -> Bool -> RTVar tv a 
setRtvPol (RTVar a i) b = RTVar a (i{rtv_is_pol = b})

rTVarToBind :: RTVar RTyVar s  -> Maybe (Symbol, s)
rTVarToBind = go . ty_var_info
  where
    go (RTVInfo {..}) | rtv_is_val = Just (rtv_name, rtv_kind)
    go _                           = Nothing

ty_var_is_val :: RTVar tv s -> Bool
ty_var_is_val = rtvinfo_is_val . ty_var_info

rtvinfo_is_val :: RTVInfo s -> Bool
rtvinfo_is_val (RTVNoInfo {..}) = False
rtvinfo_is_val (RTVInfo {..})   = rtv_is_val

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
  } deriving (Eq, Generic, Data, Typeable, Functor)
    deriving Hashable via Generically (Ref τ t)

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
  }
  deriving (Eq, Generic, Data, Typeable, Functor, Foldable, Traversable)
  deriving Hashable via Generically (UReft r)

instance B.Binary r => B.Binary (UReft r)

type BRType      = RType BTyCon BTyVar       -- ^ "Bare" parsed version
type RRType      = RType RTyCon RTyVar       -- ^ "Resolved" version
type RRep        = RTypeRep RTyCon RTyVar
type BSort       = BRType    ()
type RSort       = RRType    ()
type BPVar       = PVar      BSort
type RPVar       = PVar      RSort
type RReft       = UReft     F.Reft
type PrType      = RRType    Predicate
type BareType    = BRType    RReft
type SpecType    = RRType    RReft
type SpecRep     = RRep      RReft
type SpecProp    = RRProp    RReft
type RRProp r    = Ref       RSort (RRType r)
type BRProp r    = Ref       BSort (BRType r)
type SpecRTVar   = RTVar     RTyVar RSort 



type LocBareType = F.Located BareType
type LocSpecType = F.Located SpecType

type SpecRTEnv   = RTEnv RTyVar SpecType 
type BareRTEnv   = RTEnv Symbol BareType 
type BareRTAlias = RTAlias Symbol BareType 
type SpecRTAlias = RTAlias RTyVar SpecType


class SubsTy tv ty a where
  subt :: (tv, ty) -> a -> a

class (Eq c) => TyConable c where
  isFun    :: c -> Bool
  isList   :: c -> Bool
  isTuple  :: c -> Bool
  ppTycon  :: c -> Doc
  isClass  :: c -> Bool
  isEmbeddedDict :: c -> Bool
  isEqual  :: c -> Bool
  isOrdCls  :: c -> Bool
  isEqCls   :: c -> Bool

  isNumCls  :: c -> Bool
  isFracCls :: c -> Bool

  isClass   = const False
  isEmbeddedDict c = isNumCls c || isEqual c || isOrdCls c || isEqCls c
  isOrdCls  = const False
  isEqCls   = const False
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
  isTuple    = Ghc.isTupleTyCon   . rtc_tc
  isClass    = isClass . rtc_tc -- isClassRTyCon
  isEqual    = isEqual . rtc_tc
  ppTycon    = F.toFix

  isNumCls c  = maybe False (isClassOrSubClass isNumericClass)
                (tyConClass_maybe $ rtc_tc c)
  isFracCls c = maybe False (isClassOrSubClass isFractionalClass)
                (tyConClass_maybe $ rtc_tc c)
  isOrdCls  c = maybe False isOrdClass (tyConClass_maybe $ rtc_tc c)
  isEqCls   c = isEqCls (rtc_tc c)


instance TyConable TyCon where
  isFun      = isFunTyCon
  isList     = (listTyCon ==)
  isTuple    = Ghc.isTupleTyCon
  isClass c  = isClassTyCon c   || isEqual c -- c == eqPrimTyCon
  isEqual c  = c == eqPrimTyCon || c == eqReprPrimTyCon
  ppTycon    = text . showPpr

  isNumCls c  = maybe False (isClassOrSubClass isNumericClass)
                (tyConClass_maybe $ c)
  isFracCls c = maybe False (isClassOrSubClass isFractionalClass)
                (tyConClass_maybe $ c)
  isOrdCls c  = maybe False isOrdClass
                (tyConClass_maybe c)
  isEqCls  c  = isPrelEqTyCon c

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

instance Ord BTyCon where 
  compare x y = compare (btc_tc x) (btc_tc y)

instance F.Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c

instance F.Fixpoint BTyCon where
  toFix = text . F.symbolString . F.val . btc_tc

instance F.Fixpoint Cinfo where
  toFix = text . showPpr . ci_loc

instance Show Cinfo where
  show = show . F.toFix

instance F.PPrint RTyCon where
  pprintTidy k c 
    | ppDebug ppEnv = F.pprintTidy k tc  <-> (angleBrackets $ F.pprintTidy k pvs)
    | otherwise     = text . showPpr . rtc_tc $ c
    where 
      tc            = F.symbol (rtc_tc c) 
      pvs           = rtc_pvars c 

instance F.PPrint BTyCon where
  pprintTidy _ = text . F.symbolString . F.val . btc_tc

instance F.PPrint v => F.PPrint (RTVar v s) where
  pprintTidy k (RTVar x _) = F.pprintTidy k x

instance Show RTyCon where
  show = F.showpp

instance Show BTyCon where
  show = F.showpp

instance F.Loc BTyCon where 
  srcSpan = F.srcSpan . btc_tc 

--------------------------------------------------------------------------------
-- | Refined Instances ---------------------------------------------------------
--------------------------------------------------------------------------------

data RInstance t = RI
  { riclass :: BTyCon
  , ritype  :: [t]
  , risigs  :: [(F.LocSymbol, RISig t)]
  } deriving (Eq, Generic, Functor, Data, Typeable, Show)
    deriving Hashable via Generically (RInstance t)

data RILaws ty = RIL
  { rilName    :: BTyCon
  , rilSupers  :: [ty]
  , rilTyArgs  :: [ty]
  , rilEqus    :: [(F.LocSymbol, F.LocSymbol)]
  , rilPos     :: F.Located ()
  } deriving (Eq, Show, Functor, Data, Typeable, Generic)
    deriving Hashable via Generically (RILaws ty)

data RISig t = RIAssumed t | RISig t
  deriving (Eq, Generic, Functor, Data, Typeable, Show)
  deriving Hashable via Generically (RISig t)

instance F.PPrint t => F.PPrint (RISig t) where
  pprintTidy k = ppRISig k (empty :: Doc) 

ppRISig :: (F.PPrint k, F.PPrint t) => F.Tidy -> k -> RISig t -> Doc
ppRISig k x (RIAssumed t) = "assume" <+> F.pprintTidy k x <+> "::" <+> F.pprintTidy k t 
ppRISig k x (RISig t)     =              F.pprintTidy k x <+> "::" <+> F.pprintTidy k t 

instance F.PPrint t => F.PPrint (RInstance t) where
  pprintTidy k (RI n ts mts) = ppMethods k "instance" n ts mts 

  
instance (B.Binary t) => B.Binary (RInstance t)
instance (B.Binary t) => B.Binary (RISig t)
instance (B.Binary t) => B.Binary (RILaws t)

newtype DEnv x ty = DEnv (M.HashMap x (M.HashMap Symbol (RISig ty)))
                    deriving (Semigroup, Monoid, Show, Functor)

type RDEnv = DEnv Var SpecType

data MethodType t = MT {tyInstance :: !(Maybe t), tyClass :: !(Maybe t) }
  deriving (Show)

getMethodType :: MethodType t -> Maybe t 
getMethodType (MT (Just t) _ ) = Just t 
getMethodType (MT _ t) = t 

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

-- type AxiomEq = F.Equation

instance Show (Axiom Var Type CoreExpr) where
  show (Axiom (n, c) v bs _ts lhs rhs) = "Axiom : " ++
                                         "\nFun Name: " ++ (showPpr n) ++
                                         "\nReal Name: " ++ (showPpr v) ++
                                         "\nData Con: " ++ (showPpr c) ++
                                         "\nArguments:" ++ (showPpr bs)  ++
                                         -- "\nTypes    :" ++ (showPpr ts)  ++
                                         "\nLHS      :" ++ (showPpr lhs) ++
                                         "\nRHS      :" ++ (showPpr rhs)

--------------------------------------------------------------------------------
-- | Data type refinements
--------------------------------------------------------------------------------
data DataDecl   = DataDecl
  { tycName   :: DataName              -- ^ Type  Constructor Name
  , tycTyVars :: [Symbol]              -- ^ Tyvar Parameters
  , tycPVars  :: [PVar BSort]          -- ^ PVar  Parameters
  , tycDCons  :: Maybe [DataCtor]      -- ^ Data Constructors (Nothing is reserved for non-GADT style empty data declarations)
  , tycSrcPos :: !F.SourcePos          -- ^ Source Position
  , tycSFun   :: Maybe SizeFun         -- ^ Default termination measure
  , tycPropTy :: Maybe BareType        -- ^ Type of Ind-Prop
  , tycKind   :: !DataDeclKind         -- ^ User-defined or Auto-lifted
  } deriving (Data, Typeable, Generic)
    deriving Hashable via Generically DataDecl

-- | The name of the `TyCon` corresponding to a `DataDecl`
data DataName
  = DnName !F.LocSymbol                -- ^ for 'isVanillyAlgTyCon' we can directly use the `TyCon` name
  | DnCon  !F.LocSymbol                -- ^ for 'FamInst' TyCon we save some `DataCon` name
  deriving (Eq, Ord, Data, Typeable, Generic)

-- | Data Constructor
data DataCtor = DataCtor
  { dcName   :: F.LocSymbol            -- ^ DataCon name
  , dcTyVars :: [F.Symbol]             -- ^ Type parameters
  , dcTheta  :: [BareType]             -- ^ The GHC ThetaType corresponding to DataCon.dataConSig
  , dcFields :: [(Symbol, BareType)]   -- ^ field-name and field-Type pairs 
  , dcResult :: Maybe BareType         -- ^ Possible output (if in GADT form)
  } deriving (Data, Typeable, Generic)
    deriving Hashable via Generically DataCtor

-- | Termination expressions
data SizeFun
  = IdSizeFun              -- ^ \x -> F.EVar x
  | SymSizeFun F.LocSymbol -- ^ \x -> f x
  deriving (Data, Typeable, Generic)
  deriving Hashable via Generically SizeFun

-- | What kind of `DataDecl` is it?
data DataDeclKind
  = DataUser           -- ^ User defined data-definitions         (should have refined fields)
  | DataReflected      -- ^ Automatically lifted data-definitions (do not have refined fields)
  deriving (Eq, Data, Typeable, Generic, Show)
  deriving Hashable via Generically DataDeclKind

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

instance F.PPrint HasDataDecl where
  pprintTidy _ HasDecl    = text "HasDecl"
  pprintTidy k (NoDecl z) = text "NoDecl" <+> parens (F.pprintTidy k z)

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
  , rtVArgs :: [Symbol]           -- ^ value parameters
  , rtBody  :: a                  -- ^ what the alias expands to
  -- , rtMod   :: !ModName           -- ^ module where alias was defined
  } deriving (Eq, Data, Typeable, Generic, Functor)
    deriving Hashable via Generically (RTAlias x a)
-- TODO support ghosts in aliases?

instance (B.Binary x, B.Binary a) => B.Binary (RTAlias x a)

mapRTAVars :: (a -> b) -> RTAlias a ty -> RTAlias b ty
mapRTAVars f rt = rt { rtTArgs = f <$> rtTArgs rt }

lmapEAlias :: LMap -> F.Located (RTAlias Symbol Expr)
lmapEAlias (LMap v ys e) = F.atLoc v (RTA (F.val v) [] ys e) -- (F.loc v) (F.loc v)


--------------------------------------------------------------------------------
-- | Constructor and Destructors for RTypes ------------------------------------
--------------------------------------------------------------------------------
data RTypeRep c tv r = RTypeRep
  { ty_vars   :: [(RTVar tv (RType c tv ()), r)]
  , ty_preds  :: [PVar (RType c tv ())]
  , ty_ebinds :: [Symbol]
  , ty_einfo  :: [RFInfo]
  , ty_erefts :: [r]
  , ty_eargs  :: [RType c tv r]
  , ty_binds  :: [Symbol]
  , ty_info   :: [RFInfo]
  , ty_refts  :: [r]
  , ty_args   :: [RType c tv r]
  , ty_res    :: (RType c tv r)
  }

fromRTypeRep :: RTypeRep c tv r -> RType c tv r
fromRTypeRep (RTypeRep {..})
  = mkArrow ty_vars ty_preds earrs arrs ty_res
  where
    arrs  = safeZip4WithError ("fromRTypeRep: " ++ show (length ty_binds, length ty_info, length ty_args, length ty_refts)) ty_binds ty_info ty_args ty_refts
    earrs = safeZip4WithError ("fromRTypeRep: " ++ show (length ty_ebinds, length ty_einfo, length ty_eargs, length ty_erefts)) ty_ebinds ty_einfo ty_eargs ty_erefts

--------------------------------------------------------------------------------
toRTypeRep           :: RType c tv r -> RTypeRep c tv r
--------------------------------------------------------------------------------
toRTypeRep t         = RTypeRep αs πs xs' is' rs' ts' xs is rs ts t''
  where
    (αs, πs, t')  = bkUniv  t
    ((xs',is', ts',rs'),(xs, is, ts, rs), t'') = bkArrow t'

mkArrow :: [(RTVar tv (RType c tv ()), r)]
        -> [PVar (RType c tv ())]
        -> [(Symbol, RFInfo, RType c tv r, r)]
        -> [(Symbol, RFInfo, RType c tv r, r)]
        -> RType c tv r
        -> RType c tv r
mkArrow αs πs yts xts = mkUnivs αs πs . mkArrs RImpF yts. mkArrs RFun xts
  where
    mkArrs f xts t  = foldr (\(b,i,t1,r) t2 -> f b i t1 t2 r) t xts

-- Do I need to keep track of implicits here too?
bkArrowDeep :: RType t t1 a -> ([Symbol], [RFInfo], [RType t t1 a], [a], RType t t1 a)
bkArrowDeep (RAllT _ t _)   = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RImpF x i t t' r)= bkArrowDeep (RFun x i t t' r)
bkArrowDeep (RFun x i t t' r) = let (xs, is, ts, rs, t'') = bkArrowDeep t'  in (x:xs, i:is, t:ts, r:rs, t'')
bkArrowDeep t               = ([], [], [], [], t)

bkArrow :: RType t t1 a -> ( ([Symbol], [RFInfo], [RType t t1 a], [a])
                           , ([Symbol], [RFInfo], [RType t t1 a], [a])
                           , RType t t1 a )
bkArrow t                = ((xs,is,ts,rs),(xs',is',ts',rs'),t'')
  where 
    (xs, is, ts, rs, t')     = bkImp t
    (xs', is', ts', rs', t'') = bkFun t'


bkFun :: RType t t1 a -> ([Symbol], [RFInfo], [RType t t1 a], [a], RType t t1 a)
bkFun (RFun x i t t' r) = let (xs, is, ts, rs, t'') = bkFun t'  in (x:xs, i:is, t:ts, r:rs, t'')
bkFun t                 = ([], [], [], [], t)

bkImp :: RType t t1 a -> ([Symbol], [RFInfo], [RType t t1 a], [a], RType t t1 a)
bkImp (RImpF x i t t' r) = let (xs, is, ts, rs, t'') = bkImp t'  in (x:xs, i:is, t:ts, r:rs, t'')
bkImp t                  = ([], [], [], [], t)

safeBkArrow ::(F.PPrint (RType t t1 a)) 
            => RType t t1 a -> ( ([Symbol], [RFInfo], [RType t t1 a], [a])
                               , ([Symbol], [RFInfo], [RType t t1 a], [a])
                               , RType t t1 a )
safeBkArrow t@(RAllT _ _ _) = Prelude.error {- panic Nothing -} $ "safeBkArrow on RAllT" ++ F.showpp t
safeBkArrow (RAllP _ _)     = Prelude.error {- panic Nothing -} "safeBkArrow on RAllP"
safeBkArrow t               = bkArrow t

mkUnivs :: (Foldable t, Foldable t1)
        => t  (RTVar tv (RType c tv ()), r)
        -> t1 (PVar (RType c tv ()))
        -> RType c tv r
        -> RType c tv r
mkUnivs αs πs t = foldr (\(a,r) t -> RAllT a t r) (foldr RAllP t πs) αs

bkUnivClass :: SpecType -> ([(SpecRTVar, RReft)],[PVar RSort], [(RTyCon, [SpecType])], SpecType )
bkUnivClass t        = (as, ps, cs, t2) 
  where 
    (as, ps, t1) = bkUniv  t
    (cs, t2)     = bkClass t1


bkUniv :: RType tv c r -> ([(RTVar c (RType tv c ()), r)], [PVar (RType tv c ())], RType tv c r)
bkUniv (RAllT α t r) = let (αs, πs, t') = bkUniv t in ((α, r):αs, πs, t')
bkUniv (RAllP π t)   = let (αs, πs, t') = bkUniv t in (αs, π:πs, t')
bkUniv t             = ([], [], t)


-- bkFun :: RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
-- bkFun (RFun x t t' r) = let (xs, ts, rs, t'') = bkFun t'  in (x:xs, t:ts, r:rs, t'')
-- bkFun t               = ([], [], [], t)

bkUnivClass' :: SpecType ->
  ([(SpecRTVar, RReft)], [PVar RSort], [(Symbol, SpecType, RReft)], SpecType)
bkUnivClass' t = (as, ps, zip3 bs ts rs, t2)
  where
    (as, ps, t1) = bkUniv  t
    (bs, ts, rs, t2)     = bkClass' t1

bkClass' :: TyConable t => RType t t1 a -> ([Symbol], [RType t t1 a], [a], RType t t1 a)
bkClass' (RImpF x _ t@(RApp c _ _ _) t' r)
  | isClass c
  = let (xs, ts, rs, t'') = bkClass' t' in (x:xs, t:ts, r:rs, t'')
bkClass' (RFun x _ t@(RApp c _ _ _) t' r)
  | isClass c
  = let (xs, ts, rs, t'') = bkClass' t' in (x:xs, t:ts, r:rs, t'')
bkClass' (RRTy e r o t)
  = let (xs, ts, rs, t'') = bkClass' t in (xs, ts, rs, RRTy e r o t'')
bkClass' t
  = ([], [],[],t)

bkClass :: (F.PPrint c, TyConable c) => RType c tv r -> ([(c, [RType c tv r])], RType c tv r)
bkClass (RImpF _ _ (RApp c t _ _) t' _)
  | isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RFun _ _ (RApp c t _ _) t' _)
  | F.notracepp ("IS-CLASS: " ++ F.showpp c) $ isClass c
  = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass (RRTy e r o t)
  = let (cs, t') = bkClass t in (cs, RRTy e r o t')
bkClass t
  = ([], t)

rImpF :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rImpF b t t' = RImpF b defRFInfo t t' mempty

rFun :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun b t t' = RFun b defRFInfo t t' mempty

rFun' :: Monoid r => RFInfo -> Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFun' i b t t' = RFun b i t t' mempty

rFunDebug :: Monoid r => Symbol -> RType c tv r -> RType c tv r -> RType c tv r
rFunDebug b t t' = RFun b (classRFInfo True) t t' mempty

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

class F.Reftable r => UReftable r where
  ofUReft :: UReft F.Reft -> r
  ofUReft (MkUReft r _) = F.ofReft r


instance UReftable (UReft F.Reft) where
   ofUReft r = r

instance UReftable () where
   ofUReft _ = mempty

instance (F.PPrint r, F.Reftable r) => F.Reftable (UReft r) where
  isTauto               = isTauto_ureft
  ppTy                  = ppTy_ureft
  toReft (MkUReft r ps) = F.toReft r `F.meet` F.toReft ps
  params (MkUReft r _)  = F.params r
  bot (MkUReft r _)     = MkUReft (F.bot r) (Pr [])
  top (MkUReft r p)     = MkUReft (F.top r) (F.top p)
  ofReft r              = MkUReft (F.ofReft r) mempty

instance F.Expression (UReft ()) where
  expr = F.expr . F.toReft



isTauto_ureft :: F.Reftable r => UReft r -> Bool
isTauto_ureft u      = F.isTauto (ur_reft u) && F.isTauto (ur_pred u) 

ppTy_ureft :: F.Reftable r => UReft r -> Doc -> Doc
ppTy_ureft u@(MkUReft r p) d
  | isTauto_ureft  u  = d
  | otherwise         = ppr_reft r (F.ppTy p d)

ppr_reft :: (F.Reftable r) => r -> Doc -> Doc
ppr_reft r d = braces (F.pprint v <+> colon <+> d <+> text "|" <+> F.pprint r')
  where
    r'@(F.Reft (v, _)) = F.toReft r

instance F.Subable r => F.Subable (UReft r) where
  syms (MkUReft r p)     = F.syms r ++ F.syms p
  subst s (MkUReft r z)  = MkUReft (F.subst s r)  (F.subst s z)  
  substf f (MkUReft r z) = MkUReft (F.substf f r) (F.substf f z) 
  substa f (MkUReft r z) = MkUReft (F.substa f r) (F.substa f z) 

instance (F.Reftable r, TyConable c) => F.Subable (RTProp c tv r) where
  syms (RProp  ss r)     = (fst <$> ss) ++ F.syms r

  subst su (RProp ss (RHole r)) = RProp ss (RHole (F.subst su r))
  subst su (RProp  ss t) = RProp ss (F.subst su <$> t)

  substf f (RProp ss (RHole r)) = RProp ss (RHole (F.substf f r))
  substf f (RProp  ss t) = RProp ss (F.substf f <$> t)

  substa f (RProp ss (RHole r)) = RProp ss (RHole (F.substa f r))
  substa f (RProp  ss t) = RProp ss (F.substa f <$> t)


instance (F.Subable r, F.Reftable r, TyConable c) => F.Subable (RType c tv r) where
  syms        = foldReft False (\_ r acc -> F.syms r ++ acc) []
  -- 'substa' will substitute bound vars
  substa f    = emapExprArg (\_ -> F.substa f) []      . mapReft  (F.substa f)
  -- 'substf' will NOT substitute bound vars
  substf f    = emapExprArg (\_ -> F.substf f) []      . emapReft (F.substf . F.substfExcept f) []
  subst su    = emapExprArg (\_ -> F.subst su) []      . emapReft (F.subst  . F.substExcept su) []
  subst1 t su = emapExprArg (\_ e -> F.subst1 e su) [] $ emapReft (\xs r -> F.subst1Except xs r su) [] t


instance F.Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = panic Nothing "No BOT instance for Predicate"
  ppTy r d | F.isTauto r      = d
           | not (ppPs ppEnv) = d
           | otherwise        = d <-> (angleBrackets $ F.pprint r)

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

--------------------------------------------------------------------------------
-- | Visitors ------------------------------------------------------------------
--------------------------------------------------------------------------------
mapExprReft :: (Symbol -> Expr -> Expr) -> RType c tv RReft -> RType c tv RReft
mapExprReft f = mapReft g
  where
    g (MkUReft (F.Reft (x, e)) p) = MkUReft (F.Reft (x, f x e)) p

-- const False (not dropping dict) is probably fine since there will not be refinement on
-- dictionaries
isTrivial :: (F.Reftable r, TyConable c) => RType c tv r -> Bool
isTrivial t = foldReft False (\_ r b -> F.isTauto r && b) True t

mapReft ::  (r1 -> r2) -> RType c tv r1 -> RType c tv r2
mapReft f = emapReft (const f) []

emapReft ::  ([Symbol] -> r1 -> r2) -> [Symbol] -> RType c tv r1 -> RType c tv r2
emapReft f γ (RVar α r)          = RVar  α (f γ r)
emapReft f γ (RAllT α t r)       = RAllT α (emapReft f γ t) (f γ r)
emapReft f γ (RAllP π t)         = RAllP π (emapReft f γ t)
emapReft f γ (RImpF x i t t' r)  = RImpF x i (emapReft f γ t) (emapReft f (x:γ) t') (f (x:γ) r)
emapReft f γ (RFun x i t t' r)   = RFun  x i (emapReft f γ t) (emapReft f (x:γ) t') (f (x:γ) r)
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
    go γ (RAllT α t r)      = RAllT α (go γ t) r 
    go γ (RAllP π t)        = RAllP π (go γ t)
    go γ (RImpF x i t t' r) = RImpF x i (go γ t) (go (x:γ) t') r
    go γ (RFun x i t t' r)  = RFun  x i (go γ t) (go (x:γ) t') r
    go γ (RApp c ts rs r)   = RApp  c (go γ <$> ts) (mo γ <$> rs) r
    go γ (RAllE z t t')     = RAllE z (go γ t) (go γ t')
    go γ (REx z t t')       = REx   z (go γ t) (go γ t')
    go γ (RExprArg e)       = RExprArg (f γ <$> F.notracepp "RExprArg" e) -- <---- actual substitution
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
    go a (RAllT _ t _)      = step a t
    go a (RAllP _ t)        = step a t
    go a (RImpF _ _ t t' _) = foldl' step a [t, t']
    go a (RFun _ _ t t' _)  = foldl' step a [t, t']
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
isBase (RAllT _ t _)    = isBase t
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RImpF _ _ _ _ _)  = False
isBase (RFun _ _ _ _ _)   = False
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase (RRTy _ _ _ t)   = isBase t
isBase (RAllE _ _ t)    = isBase t
isBase (REx _ _ t)      = isBase t
isBase _                = False

hasHoleTy :: RType t t1 t2 -> Bool
hasHoleTy (RVar _ _)       = False 
hasHoleTy (RAllT _ t _)    = hasHoleTy t 
hasHoleTy (RAllP _ t)      = hasHoleTy t
hasHoleTy (RImpF _ _ t t' _) = hasHoleTy t || hasHoleTy t'
hasHoleTy (RFun _ _ t t' _)  = hasHoleTy t || hasHoleTy t'
hasHoleTy (RApp _ ts _ _)  = any hasHoleTy ts 
hasHoleTy (RAllE _ t t')   = hasHoleTy t || hasHoleTy t'
hasHoleTy (REx _ t t')     = hasHoleTy t || hasHoleTy t'
hasHoleTy (RExprArg _)     = False 
hasHoleTy (RAppTy t t' _)  = hasHoleTy t || hasHoleTy t'
hasHoleTy (RHole _)        = True 
hasHoleTy (RRTy xts _ _ t) = hasHoleTy t || any hasHoleTy (snd <$> xts)



isFunTy :: RType t t1 t2 -> Bool
isFunTy (RAllE _ _ t)    = isFunTy t
isFunTy (RAllT _ t _)    = isFunTy t
isFunTy (RAllP _ t)      = isFunTy t
isFunTy (RImpF _ _ _ _ _)= True
isFunTy (RFun _ _ _ _ _) = True
isFunTy _                = False


mapReftM :: (Monad m) => (r1 -> m r2) -> RType c tv r1 -> m (RType c tv r2)
mapReftM f (RVar α r)         = liftM   (RVar  α)   (f r)
mapReftM f (RAllT α t r)      = liftM2  (RAllT α)   (mapReftM f t)          (f r)
mapReftM f (RAllP π t)        = liftM   (RAllP π)   (mapReftM f t)
mapReftM f (RImpF x i t t' r) = liftM3  (RImpF x i) (mapReftM f t)          (mapReftM f t')       (f r)
mapReftM f (RFun x i t t' r)  = liftM3  (RFun x i)  (mapReftM f t)          (mapReftM f t')       (f r)
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
mapPropM f (RAllT α t r)      = liftM2  (RAllT α)   (mapPropM f t)          (return r)
mapPropM f (RAllP π t)        = liftM   (RAllP π)   (mapPropM f t)
mapPropM f (RImpF x i t t' r) = liftM3  (RImpF x i)    (mapPropM f t)         (mapPropM f t') (return r)
mapPropM f (RFun x i t t' r)  = liftM3  (RFun x i)    (mapPropM f t)          (mapPropM f t') (return r)
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
foldReft :: (F.Reftable r, TyConable c) => BScope -> (F.SEnv (RType c tv r) -> r -> a -> a) -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft bsc f = foldReft'  (\_ _ -> False) bsc id (\γ _ -> f γ)

--------------------------------------------------------------------------------
foldReft' :: (F.Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> BScope
          -> (RType c tv r -> b)
          -> (F.SEnv b -> Maybe (RType c tv r) -> r -> a -> a)
          -> a -> RType c tv r -> a
--------------------------------------------------------------------------------
foldReft' logicBind bsc g f 
  = efoldReft logicBind bsc 
              (\_ _ -> [])
              (\_ -> [])
              g
              (\γ t r z -> f γ t r z)
              (\_ γ -> γ)
              F.emptySEnv



-- efoldReft :: F.Reftable r =>(p -> [RType c tv r] -> [(Symbol, a)])-> (RType c tv r -> a)-> (SEnv a -> Maybe (RType c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType c tv r-> c1
efoldReft :: (F.Reftable r, TyConable c)
          => (Symbol -> RType c tv r -> Bool)
          -> BScope
          -> (c  -> [RType c tv r] -> [(Symbol, a)])
          -> (RTVar tv (RType c tv ()) -> [(Symbol, a)])
          -> (RType c tv r -> a)
          -> (F.SEnv a -> Maybe (RType c tv r) -> r -> b -> b)
          -> (PVar (RType c tv ()) -> F.SEnv a -> F.SEnv a)
          -> F.SEnv a
          -> b
          -> RType c tv r
          -> b
efoldReft logicBind bsc cb dty g f fp = go
  where
    -- folding over RType
    go γ z me@(RVar _ r)                = f γ (Just me) r z
    go γ z me@(RAllT a t r)
       | ty_var_is_val a                = f γ (Just me) r (go (insertsSEnv γ (dty a)) z t)
       | otherwise                      = f γ (Just me) r (go γ z t)
    go γ z (RAllP p t)                  = go (fp p γ) z t
    go γ z (RImpF x i t t' r)             = go γ z (RFun x i t t' r)
    go γ z me@(RFun _ RFInfo{permitTC = permitTC} (RApp c ts _ _) t' r)
       | (if permitTC == Just True then isEmbeddedDict else isClass)
         c  = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t')
    go γ z me@(RFun x _ t t' r)
       | logicBind x t                  = f γ (Just me) r (go γ' (go γ z t) t')
       | otherwise                      = f γ (Just me) r (go γ  (go γ z t) t')
       where
         γ'                             = insertSEnv x (g t) γ
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' γ' z ts) rs)
       where γ' = if bsc then insertSEnv (rTypeValueVar me) (g me) γ else γ 

    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t'
    go γ z me@(RRTy [] r _ t)           = f γ (Just me) r (go γ z t)
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

mapRFInfo :: (RFInfo -> RFInfo) -> RType c tv r -> RType c tv r
mapRFInfo f (RAllT α t r)     = RAllT α (mapRFInfo f t) r
mapRFInfo f (RAllP π t)       = RAllP π (mapRFInfo f t)
mapRFInfo f (RImpF x i t t' r) = RImpF x (f i) (mapRFInfo f t) (mapRFInfo f t') r
mapRFInfo f (RFun x i t t' r)  = RFun x (f i) (mapRFInfo f t) (mapRFInfo f t') r
mapRFInfo f (RAppTy t t' r)   = RAppTy (mapRFInfo f t) (mapRFInfo f t') r
mapRFInfo f (RApp c ts rs r)  = RApp c (mapRFInfo f <$> ts) (mapRFInfoRef f <$> rs) r
mapRFInfo f (REx b t1 t2)     = REx b  (mapRFInfo f t1) (mapRFInfo f t2)
mapRFInfo f (RAllE b t1 t2)   = RAllE b  (mapRFInfo f t1) (mapRFInfo f t2)
mapRFInfo f (RRTy e r o t)    = RRTy (mapSnd (mapRFInfo f) <$> e) r o (mapRFInfo f t)
mapRFInfo _ t'                = t'

mapRFInfoRef :: (RFInfo -> RFInfo)
          -> Ref τ (RType c tv r) -> Ref τ (RType c tv r)
mapRFInfoRef _ (RProp s (RHole r)) = RProp s $ RHole r
mapRFInfoRef f (RProp s t)    = RProp  s $ mapRFInfo f t

mapBot :: (RType c tv r -> RType c tv r) -> RType c tv r -> RType c tv r
mapBot f (RAllT α t r)     = RAllT α (mapBot f t) r
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RImpF x i t t' r) = RImpF x i (mapBot f t) (mapBot f t') r
mapBot f (RFun x i t t' r)  = RFun x i (mapBot f t) (mapBot f t') r
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
mapBind f (RAllT α t r)    = RAllT α (mapBind f t) r
mapBind f (RAllP π t)      = RAllP π (mapBind f t)
mapBind f (RImpF b i t1 t2 r)= RImpF (f b) i (mapBind f t1) (mapBind f t2) r
mapBind f (RFun b i t1 t2 r) = RFun (f b) i (mapBind f t1) (mapBind f t2) r
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
stripAnnotations (RAllT α t r)    = RAllT α (stripAnnotations t) r
stripAnnotations (RAllP _ t)      = stripAnnotations t
stripAnnotations (RAllE _ _ t)    = stripAnnotations t
stripAnnotations (REx _ _ t)      = stripAnnotations t
stripAnnotations (RImpF x i t t' r) = RImpF x i (stripAnnotations t) (stripAnnotations t') r
stripAnnotations (RFun x i t t' r)  = RFun x i (stripAnnotations t) (stripAnnotations t') r
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
stripRTypeBase (RImpF _ _ _ _ x)
  = Just x
stripRTypeBase (RFun _ _ _ _ x)
  = Just x
stripRTypeBase (RAppTy _ _ x)
  = Just x
stripRTypeBase (RAllT _ _ x)
  = Just x 
stripRTypeBase _
  = Nothing

topRTypeBase :: (F.Reftable r) => RType c tv r -> RType c tv r
topRTypeBase = mapRBase F.top

mapRBase :: (r -> r) -> RType c tv r -> RType c tv r
mapRBase f (RApp c ts rs r) = RApp c ts rs $ f r
mapRBase f (RVar a r)       = RVar a $ f r
mapRBase f (RImpF x i t1 t2 r)= RImpF x i t1 t2 $ f r
mapRBase f (RFun x i t1 t2 r) = RFun x i t1 t2 $ f r
mapRBase f (RAppTy t1 t2 r) = RAppTy t1 t2 $ f r
mapRBase _ t                = t

-----------------------------------------------------------------------------
-- | F.PPrint -----------------------------------------------------------------
-----------------------------------------------------------------------------

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

type REnv = AREnv SpecType 

data AREnv t = REnv
  { reGlobal :: M.HashMap Symbol t -- ^ the "global" names for module
  , reLocal  :: M.HashMap Symbol t -- ^ the "local" names for sub-exprs
  }

instance Functor AREnv where 
  fmap f (REnv g l) = REnv (fmap f g) (fmap f l)

instance (F.PPrint t) => F.PPrint (AREnv t) where
  pprintTidy k re =
    "RENV LOCAL"
    $+$
    ""
    $+$
    F.pprintTidy k (reLocal re)
    $+$
    ""
    $+$
    "RENV GLOBAL"
    $+$
    ""
    $+$
    F.pprintTidy k (reGlobal re)

instance Semigroup REnv where 
  REnv g1 l1 <> REnv g2 l2 = REnv (g1 <> g2) (l1 <> l2)  

instance Monoid REnv where 
  mempty = REnv mempty mempty

instance NFData REnv where
  rnf (REnv {}) = ()

--------------------------------------------------------------------------------
-- | Diagnostic info -----------------------------------------------------------
--------------------------------------------------------------------------------

data Warning = Warning {
    warnSpan :: SrcSpan
  , warnDoc  :: Doc
  } deriving (Eq, Show)

mkWarning :: SrcSpan -> Doc -> Warning
mkWarning = Warning

data Diagnostics = Diagnostics {
    dWarnings :: [Warning]
  , dErrors   :: [Error]
  } deriving Eq

instance Semigroup Diagnostics where
  (Diagnostics w1 e1) <> (Diagnostics w2 e2) = Diagnostics (w1 <> w2) (e1 <> e2)

instance Monoid Diagnostics where
  mempty  = emptyDiagnostics
  mappend = (<>)

mkDiagnostics :: [Warning] -> [Error] -> Diagnostics
mkDiagnostics = Diagnostics

emptyDiagnostics :: Diagnostics
emptyDiagnostics = Diagnostics mempty mempty

noErrors :: Diagnostics -> Bool
noErrors = L.null . dErrors

allWarnings :: Diagnostics -> [Warning]
allWarnings = dWarnings

allErrors :: Diagnostics -> [Error]
allErrors = dErrors

--------------------------------------------------------------------------------
-- | Printing Warnings ---------------------------------------------------------
--------------------------------------------------------------------------------

printWarning :: DynFlags -> Warning -> IO ()
printWarning dyn (Warning span doc) = GHC.putWarnMsg dyn span doc

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
                deriving (Eq, Generic)

instance F.Loc Cinfo where
  srcSpan = srcSpanFSrcSpan . ci_loc

instance NFData Cinfo

--------------------------------------------------------------------------------
-- | Module Names --------------------------------------------------------------
--------------------------------------------------------------------------------

data ModName = ModName !ModType !ModuleName 
  deriving (Eq, Ord, Show, Generic, Data, Typeable)

data ModType = Target | SrcImport | SpecImport 
  deriving (Eq, Ord, Show, Generic, Data, Typeable)

-- instance B.Binary ModType 
-- instance B.Binary ModName 

instance Hashable ModType 

instance Hashable ModName where
  hashWithSalt i (ModName t n) = hashWithSalt i (t, show n)

instance F.PPrint ModName where
  pprintTidy _ = text . show

instance F.Symbolic ModName where
  symbol (ModName _ m) = F.symbol m

instance F.Symbolic ModuleName where
  symbol = F.symbol . moduleNameFS


isTarget :: ModName -> Bool 
isTarget (ModName Target _) = True 
isTarget _                  = False 

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

qualifyModName :: ModName -> Symbol -> Symbol
qualifyModName n = qualifySymbol nSym
  where
    nSym         = F.symbol n

--------------------------------------------------------------------------------
-- | Refinement Type Aliases ---------------------------------------------------
--------------------------------------------------------------------------------
data RTEnv tv t = RTE
  { typeAliases :: M.HashMap Symbol (F.Located (RTAlias tv t))
  , exprAliases :: M.HashMap Symbol (F.Located (RTAlias Symbol Expr))
  }


instance Monoid (RTEnv tv t) where
  mempty  = RTE M.empty M.empty
  mappend = (<>)

instance Semigroup (RTEnv tv t) where
  RTE x y <> RTE x' y' = RTE (x `M.union` x') (y `M.union` y')

-- mapRT :: (M.HashMap Symbol (RTAlias tv t) -> M.HashMap Symbol (RTAlias tv t)) 
--      -> RTEnv tv t -> RTEnv tv t
-- mapRT f e = e { typeAliases = f (typeAliases e) }

-- mapRE :: (M.HashMap Symbol (RTAlias Symbol Expr)
--       -> M.HashMap Symbol (RTAlias Symbol Expr))
--      -> RTEnv tv t -> RTEnv tv t
-- mapRE f e = e { exprAliases = f $ exprAliases e }


--------------------------------------------------------------------------------
-- | Measures
--------------------------------------------------------------------------------
data Body
  = E Expr          -- ^ Measure Refinement: {v | v = e }
  | P Expr          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Expr   -- ^ Measure Refinement: {v | p}
  deriving (Show, Data, Typeable, Generic, Eq)
  deriving Hashable via Generically Body

data Def ty ctor = Def
  { measure :: F.LocSymbol
  , ctor    :: ctor
  , dsort   :: Maybe ty
  , binds   :: [(Symbol, Maybe ty)]    -- measure binders: the ADT argument fields
  , body    :: Body
  } deriving (Show, Data, Typeable, Generic, Eq, Functor)
    deriving Hashable via Generically (Def ty ctor)

data Measure ty ctor = M
  { msName :: F.LocSymbol
  , msSort :: ty
  , msEqns :: [Def ty ctor]
  , msKind :: !MeasureKind 
  , msUnSorted :: !UnSortedExprs -- potential unsorted expressions used at measure denifinitions
  } deriving (Eq, Data, Typeable, Generic, Functor)
    deriving Hashable via Generically (Measure ty ctor)

type UnSortedExprs = [UnSortedExpr] -- mempty = []
type UnSortedExpr  = ([F.Symbol], F.Expr)

data MeasureKind 
  = MsReflect     -- ^ due to `reflect foo` 
  | MsMeasure     -- ^ due to `measure foo` with old-style (non-haskell) equations
  | MsLifted      -- ^ due to `measure foo` with new-style haskell equations
  | MsClass       -- ^ due to `class measure` definition 
  | MsAbsMeasure  -- ^ due to `measure foo` without equations c.f. tests/pos/T1223.hs
  | MsSelector    -- ^ due to selector-fields e.g. `data Foo = Foo { fld :: Int }` 
  | MsChecker     -- ^ due to checkers  e.g. `is-F` for `data Foo = F ... | G ...` 
  deriving (Eq, Ord, Show, Data, Typeable, Generic)
  deriving Hashable via Generically MeasureKind

instance F.Loc (Measure a b) where 
  srcSpan = F.srcSpan . msName

instance Bifunctor Def where
  -- first f  (Def m ps c s bs b) = Def m (second f <$> ps) c (f <$> s) ((second (fmap f)) <$> bs) b
  -- second f (Def m ps c s bs b) = Def m ps (f c) s bs b
  first f  (Def m c s bs b) = Def m c (f <$> s) ((second (fmap f)) <$> bs) b
  second f (Def m c s bs b) = Def m (f c) s bs b


instance Bifunctor Measure where
  first  f (M n s es k u) = M n (f s) (first f <$> es) k u
  second f (M n s es k u) = M n s (second f <$> es)    k u 

instance                             B.Binary MeasureKind 
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
  pprintTidy k (Def m c _ bs body)
           = F.pprintTidy k m <+> cbsd <+> "=" <+> F.pprintTidy k body
    where
      cbsd = parens (F.pprintTidy k c <-> hsep (F.pprintTidy k `fmap` (fst <$> bs)))

instance (F.PPrint t, F.PPrint a) => F.PPrint (Measure t a) where
  pprintTidy k (M n s eqs _ _) =  F.pprintTidy k n <+> {- parens (pprintTidy k (loc n)) <+> -} "::" <+> F.pprintTidy k s
                                  $$ vcat (F.pprintTidy k `fmap` eqs)


instance F.PPrint (Measure t a) => Show (Measure t a) where
  show = F.showpp

instance F.PPrint t => F.PPrint (CMeasure t) where
  pprintTidy k (CM n s) =  F.pprintTidy k n <+> "::" <+> F.pprintTidy k s

instance F.PPrint (CMeasure t) => Show (CMeasure t) where
  show = F.showpp


instance F.Subable (Measure ty ctor) where
  syms  m     = concatMap F.syms (msEqns m) 
  substa f m  = m { msEqns = F.substa f  <$> msEqns m }
  substf f m  = m { msEqns = F.substf f  <$> msEqns m }
  subst  su m = m { msEqns = F.subst  su <$> msEqns m }
  -- substa f  (M n s es _) = M n s (F.substa f  <$> es) k
  -- substf f  (M n s es _) = M n s $ F.substf f  <$> es
  -- subst  su (M n s es _) = M n s $ F.subst  su <$> es

instance F.Subable (Def ty ctor) where
  syms (Def _ _ _ sb bd)  = (fst <$> sb) ++ F.syms bd
  substa f  (Def m c t b bd) = Def m c t b $ F.substa f  bd
  substf f  (Def m c t b bd) = Def m c t b $ F.substf f  bd
  subst  su (Def m c t b bd) = Def m c t b $ F.subst  su bd

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
  } deriving (Eq, Show, Functor, Data, Typeable, Generic)
    deriving Hashable via Generically (RClass ty)


instance F.PPrint t => F.PPrint (RClass t) where 
  pprintTidy k (RClass n ts as mts) 
                = ppMethods k ("class" <+> supers ts) n as [(m, RISig t) | (m, t) <- mts] 
    where 
      supers [] = "" 
      supers ts = tuplify (F.pprintTidy k   <$> ts) <+> "=>"
      tuplify   = parens . hcat . punctuate ", "


instance F.PPrint t => F.PPrint (RILaws t) where
  pprintTidy k (RIL n ss ts mts _) = ppEqs k ("instance laws" <+> supers ss) n ts mts 
   where 
    supers [] = "" 
    supers ts = tuplify (F.pprintTidy k   <$> ts) <+> "=>"
    tuplify   = parens . hcat . punctuate ", "


ppEqs :: (F.PPrint x, F.PPrint t, F.PPrint a, F.PPrint n) 
          => F.Tidy -> Doc -> n -> [a] -> [(x, t)] -> Doc
ppEqs k hdr name args mts 
  = vcat $ hdr <+> dName <+> "where" 
         : [ nest 4 (bind m t) | (m, t) <- mts ] 
    where 
      dName    = parens  (F.pprintTidy k name <+> dArgs)
      dArgs    = gaps    (F.pprintTidy k      <$> args)
      gaps     = hcat . punctuate " "
      bind m t = F.pprintTidy k m <+> "=" <+> F.pprintTidy k t 

ppMethods :: (F.PPrint x, F.PPrint t, F.PPrint a, F.PPrint n) 
          => F.Tidy -> Doc -> n -> [a] -> [(x, RISig t)] -> Doc
ppMethods k hdr name args mts 
  = vcat $ hdr <+> dName <+> "where" 
         : [ nest 4 (bind m t) | (m, t) <- mts ] 
    where 
      dName    = parens  (F.pprintTidy k name <+> dArgs)
      dArgs    = gaps    (F.pprintTidy k      <$> args)
      gaps     = hcat . punctuate " "
      bind m t = ppRISig k m t -- F.pprintTidy k m <+> "::" <+> F.pprintTidy k t 

instance B.Binary ty => B.Binary (RClass ty)


------------------------------------------------------------------------
-- | Var Hole Info -----------------------------------------------------
------------------------------------------------------------------------

data HoleInfo i t = HoleInfo {htype :: t, hloc :: SrcSpan, henv :: AREnv t, info :: i }

instance Functor (HoleInfo i) where 
  fmap f hinfo = hinfo{htype = f (htype hinfo), henv = fmap f (henv hinfo)}

instance (F.PPrint t) => F.PPrint (HoleInfo  i t) where
  pprintTidy k hinfo = text "type:" <+> F.pprintTidy k (htype hinfo) 
                       <+> text "\n loc:" <+> F.pprintTidy k (hloc hinfo) 
  -- to print the hole environment uncomment the following
  --                     <+> text "\n env:" <+> F.pprintTidy k (henv hinfo)

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
  mempty  = AI M.empty
  mappend = (<>)

instance Semigroup (AnnInfo a) where
  AI m1 <> AI m2 = AI $ M.unionWith (++) m1 m2

instance NFData a => NFData (AnnInfo a)

instance NFData a => NFData (Annot a)

--------------------------------------------------------------------------------
-- | Output --------------------------------------------------------------------
--------------------------------------------------------------------------------

data Output a = O
  { o_vars   :: Maybe [String]
  , o_types  :: !(AnnInfo a)
  , o_templs :: !(AnnInfo a)
  , o_bots   :: ![SrcSpan]
  , o_result :: ErrorResult
  } deriving (Typeable, Generic, Functor)

instance (F.PPrint a) => F.PPrint (Output a) where
  pprintTidy _ out = F.resultDoc (F.pprint <$> o_result out)

emptyOutput :: Output a
emptyOutput = O Nothing mempty mempty [] mempty

instance Monoid (Output a) where
  mempty  = emptyOutput
  mappend = (<>)

instance Semigroup (Output a) where
  o1 <> o2 = O { o_vars   =            sortNub <$> mappend (o_vars   o1) (o_vars   o2)
               , o_types  =                        mappend (o_types  o1) (o_types  o2)
               , o_templs =                        mappend (o_templs o1) (o_templs o2)
               , o_bots   = sortNubBy ordSrcSpan $ mappend (o_bots o1)   (o_bots   o2)
               , o_result =                        mappend (o_result o1) (o_result o2)
               }

-- Ord a 'SrcSpan' if it's meaningful to do so (i.e. we have a 'RealSrcSpan'). Otherwise we default to EQ.
ordSrcSpan :: SrcSpan -> SrcSpan -> Ordering
ordSrcSpan (RealSrcSpan r1 _) (RealSrcSpan r2 _) = r1 `compare` r2
ordSrcSpan (RealSrcSpan _ _ ) _                  = GT
ordSrcSpan _                  (RealSrcSpan _ _ ) = LT
ordSrcSpan _                  _                  = EQ


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
  | ImplictE
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

instance F.Symbolic DataCon where
  symbol = F.symbol . dataConWorkId

instance F.PPrint DataCon where
  pprintTidy _ = text . showPpr

instance Ord TyCon where 
  compare = compare `on` F.symbol 

instance Ord DataCon where 
  compare = compare `on` F.symbol 

instance F.PPrint TyThing where 
  pprintTidy _ = text . showPpr 

instance Show DataCon where
  show = F.showpp

-- instance F.Symbolic TyThing where 
--  symbol = tyThingSymbol 

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

instance Eq ctor => Semigroup (MSpec ty ctor) where
  MSpec c1 m1 cm1 im1 <> MSpec c2 m2 cm2 im2
    | (k1, k2) : _ <- dups
      -- = panic Nothing $ err (head dups)
    = uError $ err k1 k2
    | otherwise
    = MSpec (M.unionWith (++) c1 c2) (m1 `M.union` m2) (cm1 `M.union` cm2) (im1 ++ im2)
    where
      dups = [(k1, k2) | k1 <- M.keys m1 , k2 <- M.keys m2, F.val k1 == F.val k2]
      err k1 k2 = ErrDupMeas (fSrcSpan k1) (F.pprint (F.val k1)) (fSrcSpan <$> [k1, k2])


instance Eq ctor => Monoid (MSpec ty ctor) where
  mempty = MSpec M.empty M.empty M.empty []
  mappend = (<>)



--------------------------------------------------------------------------------
-- Nasty PP stuff
--------------------------------------------------------------------------------

instance F.PPrint BTyVar where
  pprintTidy _ (BTV α) = text (F.symbolString α)

instance F.PPrint RTyVar where
  pprintTidy k (RTV α)
   | ppTyVar ppEnv  = F.pprintTidy k (F.symbol α) -- shows full tyvar
   | otherwise      = ppr_tyvar_short α           -- drops the unique-suffix
   where
     ppr_tyvar_short :: TyVar -> Doc
     ppr_tyvar_short = text . showPpr

instance (F.PPrint r, F.Reftable r, F.PPrint t, F.PPrint (RType c tv r)) => F.PPrint (Ref t (RType c tv r)) where
  pprintTidy k (RProp ss s) = ppRefArgs k (fst <$> ss) <+> F.pprintTidy k s

ppRefArgs :: F.Tidy -> [Symbol] -> Doc
ppRefArgs _ [] = empty
ppRefArgs k ss = text "\\" <-> hsep (ppRefSym k <$> ss ++ [F.vv Nothing]) <+> "->"

ppRefSym :: (Eq a, IsString a, F.PPrint a) => F.Tidy -> a -> Doc
ppRefSym _ "" = text "_"
ppRefSym k s  = F.pprintTidy k s
