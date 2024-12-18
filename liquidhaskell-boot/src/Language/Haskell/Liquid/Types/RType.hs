{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains the types to represent refinement types.

module Language.Haskell.Liquid.Types.RType (

  -- * Bare Type Constructors and Variables
    BTyCon(..)
  , mkBTyCon
  -- , mkClassBTyCon, mkPromotedBTyCon
  , isClassBTyCon
  , BTyVar(..)

  -- * Refined Type Constructors
  , RTyCon (RTyCon, rtc_tc, rtc_info)
  , TyConInfo(..), defaultTyConInfo
  , rTyConPVs
  -- , isClassRTyCon
  , isClassType, isEqType, isRVar, isBool, isEmbeddedClass

  -- * Refinement Types
  , RType, RTypeV (..), Ref(..), RTProp, RTPropV, rPropP
  , RTyVar (..)
  , OkRT

  -- * Classes describing operations on `RTypes`
  , TyConable (..)

  -- * Type Variables
  , RTVar (..), RTVInfo (..)
  , makeRTVar, mapTyVarValue
  , dropTyVarInfo, rTVarToBind
  , setRtvPol

  -- * Predicate Variables
  , PVar
  , PVarV (PV, pname, parg, ptype, pargs), pvType
  , Predicate
  , PredicateV (..)

  -- * Manipulating `Predicates`
  , emapExprVM
  , mapPredicateV
  , emapPredicateVM
  , mapPVarV
  , emapPVarVM
  , emapSubstVM
  , pvars, pappSym, pApp

  -- * Refinements
  , UReft
  , UReftV(..)
  , mapUReftV
  , emapUReftVM

  -- * Parse-time entities describing refined data types
  , SizeFun, SizeFunV (..), szFun
  , TyConP   (..)

  -- * Pre-instantiated RType
  , RRType, RRProp
  , BRType, BRProp, BRPropV
  , BSort, BSortV, BPVar
  , RTVU, PVU

  -- * Instantiated RType
  , BareType
  , BareTypeLHName
  , BareTypeParsed
  , BareTypeV
  , SpecType, SpecProp, SpecRTVar
  , LocBareType
  , LocBareTypeLHName
  , LocBareTypeParsed
  , LocSpecType
  , RSort
  , UsedPVar
  , UsedPVarV
  , RPVar, RReft, RReftV

  -- * Printer Configuration
  , PPEnv (..)
  , ppEnv
  , ppEnvShort

  -- * Refined Function Info
  , RFInfo(..), defRFInfo, mkRFInfo, classRFInfo

  -- * Reftable/UReftable Instances
  , Reftable(..)
  , UReftable(..)
  , ToReftV(..)
  )
  where

import           Liquid.GHC.API as Ghc hiding ( Expr
                                                               , isFunTy
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
                                                               , ($$)
                                                               , braces
                                                               , angleBrackets
                                                               , brackets
                                                               )
import           Data.String
import           GHC.Generics
import           Prelude                          hiding  (error)

import           Control.DeepSeq
import           Data.Traversable                       (forAccumM)
import           Data.Typeable                          (Typeable)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import           Data.Hashable
import qualified Data.HashMap.Strict                    as M
import qualified Data.List                              as L
import           Data.Maybe                             (mapMaybe)
import           Data.List                              as L (nub)
import           Text.PrettyPrint.HughesPJ              hiding (first, (<>))
import           Language.Fixpoint.Misc

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Expr, ExprV(..), SubstV(..), Symbol)

import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.UX.Config


newtype RFInfo = RFInfo {permitTC :: Maybe Bool }
  deriving (Generic, Data, Typeable, Show, Eq)

defRFInfo :: RFInfo
defRFInfo = RFInfo Nothing

classRFInfo :: Bool -> RFInfo
classRFInfo b = RFInfo $ Just b

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

instance Show TyConP where
 show = F.showpp

instance F.PPrint TyConP where
  pprintTidy k tc = "data" <+> F.pprintTidy k (tcpCon tc)
                           <+> ppComm     k (tcpFreeTyVarsTy tc)
                           <+> ppComm     k (tcpFreePredTy   tc)

ppComm :: F.PPrint a => F.Tidy -> [a] -> Doc
ppComm k = parens . hsep . punctuate comma . fmap (F.pprintTidy k)

instance F.PPrint TyCon where
  pprintTidy F.Lossy = shortModules . pprDoc
    where
      shortModules = text . F.symbolString . dropModuleNames . F.symbol . render
  pprintTidy F.Full  =                pprDoc

-- | Termination expressions
type SizeFun = SizeFunV F.Symbol
data SizeFunV v
  = IdSizeFun              -- ^ \x -> F.EVar x
  | SymSizeFun (F.Located v) -- ^ \x -> f x
  deriving (Data, Typeable, Generic, Eq, Functor, Foldable, Traversable)
  deriving (B.Binary, Hashable) via Generically (SizeFunV v)

instance NFData v => NFData (SizeFunV v)

instance Show v => Show (SizeFunV v) where
  show IdSizeFun      = "IdSizeFun"
  show (SymSizeFun x) = "SymSizeFun " ++ show (F.val x)

szFun :: SizeFun -> Symbol -> Expr
szFun IdSizeFun      = F.EVar
szFun (SymSizeFun f) = \x -> F.mkEApp f [F.EVar x]

instance F.PPrint v => F.PPrint (SizeFunV v) where
  pprintTidy _ IdSizeFun      = "[id]"
  pprintTidy _ (SymSizeFun x) = brackets (F.pprint $ F.val x)


--------------------------------------------------------------------
-- | Abstract Predicate Variables ----------------------------------
--------------------------------------------------------------------

type PVar t = PVarV Symbol t
data PVarV v t = PV
  { pname :: !Symbol
  , ptype :: !t
  , parg  :: !Symbol
  , pargs :: ![(t, Symbol, F.ExprV v)]
  } deriving (Generic, Data, Typeable, Show, Functor)
  deriving B.Binary via Generically (PVarV v t)

mapPVarV :: (v -> v') -> (t -> t') -> PVarV v t -> PVarV v' t'
mapPVarV f g PV {..} =
    PV
      { ptype = g ptype
      , pargs = [ (g t, s, fmap f e) | (t, s, e) <- pargs ]
      , ..
      }

-- | A map traversal that collects the local variables in scope
emapPVarVM :: Monad m => ([Symbol] -> v -> m v') -> ([Symbol] -> t -> m t') -> PVarV v t -> m (PVarV v' t')
emapPVarVM f g pv = do
    ptype <- g (argSyms (pargs pv)) (ptype pv)
    (_, pargs) <- forAccumM [] (pargs pv) $ \ss (t, s, e) -> do
      (s:ss,) <$> ((,,) <$> g (s:ss) t <*> pure s <*> emapExprVM (f . ((s:ss) ++)) e)
    return pv{ptype, pargs}
  where
    argSyms = map (\(_, s, _) -> s)

instance Eq (PVarV v t) where
  pv == pv' = pname pv == pname pv' {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVarV v t) where
  compare (PV n _ _ _)  (PV n' _ _ _) = compare n n'

instance (NFData v, NFData t) => NFData   (PVarV v t)

instance Hashable (PVarV v a) where
  hashWithSalt i (PV n _ _ _) = hashWithSalt i n

pvType :: PVarV v t -> t
pvType = ptype

instance F.PPrint (PVar a) where
  pprintTidy _ = pprPvar

pprPvar :: PVar a -> Doc
pprPvar (PV s _ _ xts) = F.pprint s <+> hsep (F.pprint <$> dargs xts)
  where
    dargs              = map thd3 . takeWhile (\(_, x, y) -> F.EVar x /= y)

-- | A map traversal that collects the local variables in scope
emapExprVM :: Monad m => ([Symbol] -> v -> m v') -> ExprV v -> m (ExprV v')
emapExprVM f = go []
  where
    go acc = \case
      ESym c -> return $ ESym c
      ECon c -> return $ ECon c
      EVar v -> EVar <$> f acc v
      EApp e0 e1 -> EApp <$> go acc e0 <*> go acc e1
      ENeg e -> ENeg <$> go acc e
      EBin bop e0 e1 -> EBin bop <$> go acc e0 <*> go acc e1
      EIte e0 e1 e2 -> EIte <$> go acc e0 <*> go acc e1 <*> go acc e2
      ECst e s -> flip ECst s <$> go acc e
      ELam (s,srt) e -> ELam (s, srt) <$> go (s:acc) e
      ETApp e s -> flip ETApp s <$> go acc e
      ETAbs e s -> flip ETAbs s <$> go acc e
      PAnd xs -> PAnd <$> mapM (go acc) xs
      POr xs -> POr <$> mapM (go acc) xs
      PNot e -> PNot <$> go acc e
      PImp e0 e1 -> PImp <$> go acc e0 <*> go acc e1
      PIff e0 e1 -> PIff <$> go acc e0 <*> go acc e1
      PAtom brel e0 e1 -> PAtom brel <$> go acc e0 <*> go acc e1
      PKVar k su -> PKVar k <$> emapSubstVM (f . (domain su ++) . (acc ++)) su
      PAll bnds e -> PAll bnds <$> go (map fst bnds ++ acc) e
      PExist bnds e -> PExist bnds <$> go (map fst bnds ++ acc) e
      PGrad k su gi e ->
        PGrad k <$> emapSubstVM (f . (acc ++)) su <*> pure gi <*> go (domain su ++ acc) e
      ECoerc srt0 srt1 e -> ECoerc srt0 srt1 <$> go acc e

    domain (Su m) = M.keys m

emapSubstVM :: Monad m => ([Symbol] -> v -> m v') -> SubstV v -> m (SubstV v')
emapSubstVM f (Su m) = Su . M.fromList <$> mapM (traverse (emapExprVM f)) (M.toList m)

--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

type UsedPVar    = UsedPVarV Symbol
type UsedPVarV v = PVarV v ()

type Predicate = PredicateV Symbol
newtype PredicateV v = Pr [UsedPVarV v]
  deriving (Generic, Data, Typeable)
  deriving (B.Binary, Hashable) via Generically (PredicateV v)

mapPredicateV :: (v -> v') -> PredicateV v -> PredicateV v'
mapPredicateV f (Pr xs) = Pr (map (mapPVarV f (const ())) xs)

-- | A map traversal that collects the local variables in scope
emapPredicateVM :: Monad m => ([Symbol] -> v -> m v') -> PredicateV v -> m (PredicateV v')
emapPredicateVM f (Pr xs) = Pr <$> mapM (emapPVarVM f (\_ _ -> pure ())) xs

instance Ord v => Eq (PredicateV v) where
  (Pr vs) == (Pr ws)
      = and $ (length vs' == length ws') : [v == w | (v, w) <- zip vs' ws']
        where
          vs' = L.sort vs
          ws' = L.sort ws

instance NFData Predicate where
  rnf _ = ()

instance Monoid Predicate where
  mempty  = pdTrue
  mappend = (<>)

instance Semigroup Predicate where
  p <> p' = pdAnd [p, p']

instance F.PPrint Predicate where
  pprintTidy _ (Pr [])  = text "True"
  pprintTidy k (Pr pvs) = hsep $ punctuate (text "&") (F.pprintTidy k <$> pvs)

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

newtype BTyVar = BTV F.LocSymbol
  deriving (Show, Generic, Data, Typeable)
  deriving (B.Binary, Hashable) via Generically BTyVar

newtype RTyVar = RTV TyVar deriving (Generic, Data, Typeable)

instance Eq BTyVar where
  (BTV x) == (BTV y) = x == y

instance Ord BTyVar where
  compare (BTV x) (BTV y) = compare x y

instance NFData   BTyVar
instance NFData   RTyVar

instance F.Symbolic BTyVar where
  symbol (BTV tv) = F.symbol tv

instance F.Symbolic RTyVar where
  symbol (RTV tv) = F.symbol tv -- tyVarUniqueSymbol tv

-- instance F.Symbolic RTyVar where
  -- symbol (RTV tv) = F.symbol . getName $ tv
-- rtyVarUniqueSymbol  :: RTyVar -> Symbol
-- rtyVarUniqueSymbol (RTV tv) = tyVarUniqueSymbol tv
-- tyVarUniqueSymbol :: TyVar -> Symbol
-- tyVarUniqueSymbol tv = F.symbol $ show (getName tv) ++ "_" ++ show (varUnique tv)

data BTyCon = BTyCon
  { btc_tc    :: !(F.Located LHName)  -- ^ TyCon name with location information
  , btc_class :: !Bool           -- ^ Is this a class type constructor?
  , btc_prom  :: !Bool           -- ^ Is Promoted Data Con?
  }
  deriving (Generic, Data, Typeable)
  deriving (B.Binary, Hashable) via Generically BTyCon

data RTyCon = RTyCon
  { rtc_tc    :: TyCon         -- ^ GHC Type Constructor
  , rtc_pvars :: ![RPVar]      -- ^ Predicate Parameters
  , rtc_info  :: !TyConInfo    -- ^ TyConInfo
  }
  deriving (Generic, Data, Typeable)

instance F.Symbolic RTyCon where
  symbol = F.symbol . rtc_tc

instance NFData BTyCon

instance NFData RTyCon


mkBTyCon :: F.Located LHName -> BTyCon
mkBTyCon x = BTyCon x False False


-- | Accessors for @RTyCon@

isBool :: RType RTyCon t t1 -> Bool
isBool (RApp RTyCon{rtc_tc = c} _ _ _) = c == boolTyCon
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

isEqType :: TyConable c => RTypeV v c t t1 -> Bool
isEqType (RApp c _ _ _) = isEqual c
isEqType _              = False


isClassType :: TyConable c => RTypeV v c t t1 -> Bool
isClassType (RApp c _ _ _) = isClass c
isClassType _              = False

isEmbeddedClass :: TyConable c => RTypeV v c t t1 -> Bool
isEmbeddedClass (RApp c _ _ _) = isEmbeddedDict c
isEmbeddedClass _              = False


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


-------------------------------------------------------------------------------
-- | TyConable Instances -------------------------------------------------------
-------------------------------------------------------------------------------

instance TyConable RTyCon where
  isFun      = isArrowTyCon . rtc_tc
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
  isFun      = isArrowTyCon
  isList     = (listTyCon ==)
  isTuple    = Ghc.isTupleTyCon
  isClass c  = isClassTyCon c   || isEqual c -- c == eqPrimTyCon
  isEqual c  = c == eqPrimTyCon || c == eqReprPrimTyCon
  ppTycon    = text . showPpr

  isNumCls c  = maybe False (isClassOrSubClass isNumericClass)
                (tyConClass_maybe c)
  isFracCls c = maybe False (isClassOrSubClass isFractionalClass)
                (tyConClass_maybe c)
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
  isTuple = isTupleSymbol
  ppTycon   = text . F.symbolString

instance TyConable F.LocSymbol where
  isFun   = isFun   . F.val
  isList  = isList  . F.val
  isTuple = isTuple . F.val
  ppTycon = ppTycon . F.val

instance TyConable BTyCon where
  isFun b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> isFun s
    LHNResolved (LHRGHC n) _ -> n == unrestrictedFunTyConName
    _ -> False

  isList b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> isList s
    LHNResolved (LHRGHC n) _ -> n == listTyConName
    _ -> False

  isTuple b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> isTuple s
    LHNResolved (LHRGHC n) _ -> Ghc.isTupleTyConName n
    _ -> False

  isClass = isClassBTyCon

  ppTycon b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> ppTycon s
    LHNResolved rn _ -> case rn of
      LHRGHC n -> text $ showPpr n
      LHRLocal s -> ppTycon s
      LHRIndex i -> text $ "(Unknown LHRIndex " ++ show i ++ ")"
      LHRLogic _ -> ppTycon $ lhNameToResolvedSymbol $ F.val $ btc_tc b

instance Eq RTyCon where
  x == y = rtc_tc x == rtc_tc y

instance Eq BTyCon where
  x == y = btc_tc x == btc_tc y

instance Ord BTyCon where
  compare x y = compare (btc_tc x) (btc_tc y)

instance F.Fixpoint RTyCon where
  toFix (RTyCon c _ _) = text $ showPpr c

instance F.Fixpoint BTyCon where
  toFix b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> text $ F.symbolString s
    LHNResolved rn _ -> case rn of
      LHRGHC n -> text $ F.symbolString $ F.symbol n
      LHRLocal s -> text $ F.symbolString s
      LHRIndex i -> panic (Just $ fSrcSpan b) $ "toFix BTyCon: Unknown LHRIndex " ++ show i
      LHRLogic _ -> text $ F.symbolString $ lhNameToResolvedSymbol $ F.val $ btc_tc b

instance F.PPrint RTyCon where
  pprintTidy k c
    | ppDebug ppEnv = F.pprintTidy k tc  <-> angleBrackets (F.pprintTidy k pvs)
    | otherwise     = text . showPpr . rtc_tc $ c
    where
      tc            = F.symbol (rtc_tc c)
      pvs           = rtc_pvars c

instance F.PPrint BTyCon where
  pprintTidy _ b = case F.val (btc_tc b) of
    LHNUnresolved _ s -> text $ F.symbolString s
    LHNResolved rn _ -> case rn of
      LHRGHC n -> text $ F.symbolString $ F.symbol n
      LHRLocal s -> text $ F.symbolString s
      LHRIndex i -> text $ "(Unknown LHRIndex " ++ show i ++ ")"
      LHRLogic _ -> text $ F.symbolString $ lhNameToResolvedSymbol $ F.val $ btc_tc b

instance F.PPrint v => F.PPrint (RTVar v s) where
  pprintTidy k (RTVar x _) = F.pprintTidy k x

instance Show RTyCon where
  show = F.showpp

instance Show BTyCon where
  show = F.showpp

instance F.Loc BTyCon where
  srcSpan = F.srcSpan . btc_tc

defaultTyConInfo :: TyConInfo
defaultTyConInfo = TyConInfo [] [] Nothing


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

type RTVU c tv = RTVUV Symbol c tv
type RTVUV v c tv = RTVar tv (RTypeV v c tv ())
type PVU c tv = PVUV Symbol c tv
type PVUV v c tv = PVarV v (RTypeV v c tv ())

instance Show tv => Show (RTVU c tv) where
  show (RTVar t _) = show t

type RType c tv r = RTypeV Symbol c tv r
data RTypeV v c tv r
  = RVar {
      rt_var    :: !tv
    , rt_reft   :: !r
    }

  | RFun  {
      rt_bind   :: !Symbol
    , rt_rinfo  :: !RFInfo
    , rt_in     :: !(RTypeV v c tv r)
    , rt_out    :: !(RTypeV v c tv r)
    , rt_reft   :: !r
    }

  | RAllT {
      rt_tvbind :: !(RTVUV v c tv) -- RTVar tv (RType c tv ()))
    , rt_ty     :: !(RTypeV v c tv r)
    , rt_ref    :: !r
    }

  -- | "forall x y <z :: Nat, w :: Int> . TYPE"
  --               ^^^^^^^^^^^^^^^^^^^ (rt_pvbind)
  | RAllP {
      rt_pvbind :: !(PVUV v c tv)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  -- | For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
  --   * the `RProp`  denoted by `{\h -> v > h}` to
  --   * the `RTyCon` denoted by `[]`.
  | RApp  {
      rt_tycon  :: !c
    , rt_args   :: ![RTypeV v c tv r]
    , rt_pargs  :: ![RTPropV v c tv r]
    , rt_reft   :: !r
    }

  | RAllE {
      rt_bind   :: !Symbol
    , rt_allarg :: !(RTypeV v c tv r)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  | REx {
      rt_bind   :: !Symbol
    , rt_exarg  :: !(RTypeV v c tv r)
    , rt_ty     :: !(RTypeV v c tv r)
    }

  | RExprArg (F.Located (ExprV v))              -- ^ For expression arguments to type aliases
                                                --   see tests/pos/vector2.hs
  | RAppTy{
      rt_arg   :: !(RTypeV v c tv r)
    , rt_res   :: !(RTypeV v c tv r)
    , rt_reft  :: !r
    }

  | RRTy  {
      rt_env   :: ![(Symbol, RTypeV v c tv r)]
    , rt_ref   :: !r
    , rt_obl   :: !Oblig
    , rt_ty    :: !(RTypeV v c tv r)
    }

  | RHole r -- ^ let LH match against the Haskell type and add k-vars, e.g. `x:_`
            --   see tests/pos/Holes.hs
  deriving (Eq, Generic, Data, Typeable, Functor, Foldable, Traversable)
  deriving (B.Binary, Hashable) via Generically (RTypeV v c tv r)

instance (NFData c, NFData tv, NFData r)       => NFData (RType c tv r)

makeRTVar :: tv -> RTVar tv s
makeRTVar a = RTVar a (RTVNoInfo True)

instance (Eq tv) => Eq (RTVar tv s) where
  t1 == t2 = ty_var_value t1 == ty_var_value t2

data RTVar tv s = RTVar
  { ty_var_value :: tv
  , ty_var_info  :: RTVInfo s
  } deriving (Generic, Data, Typeable, Functor, Foldable, Traversable)
    deriving (B.Binary, Hashable) via Generically (RTVar tv s)

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
            } deriving (Generic, Data, Typeable, Functor, Eq, Foldable, Traversable)
              deriving (B.Binary, Hashable) via Generically (RTVInfo s)


setRtvPol :: RTVar tv a -> Bool -> RTVar tv a
setRtvPol (RTVar a i) b = RTVar a (i{rtv_is_pol = b})

rTVarToBind :: RTVar RTyVar s  -> Maybe (Symbol, s)
rTVarToBind = go . ty_var_info
  where
    go RTVInfo{..} | rtv_is_val = Just (rtv_name, rtv_kind)
    go _                        = Nothing

instance (NFData tv, NFData s)     => NFData   (RTVar tv s)
instance (NFData s)                => NFData   (RTVInfo s)

-- | @Ref@ describes `Prop τ` and `HProp` arguments applied to type constructors.
--   For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
--   * the `RProp`  denoted by `{\h -> v > h}` to
--   * the `RTyCon` denoted by `[]`.
--   Thus, @Ref@ is used for abstract-predicate (arguments) that are associated
--   with _type constructors_ i.e. whose semantics are _dependent upon_ the data-type.
--   In contrast, the `Predicate` argument in `ur_pred` in the @UReft@ applies
--   directly to any type and has semantics _independent of_ the data-type.

data Ref τ t = RProp
  { rf_args :: [(Symbol, τ)] -- ^ arguments. e.g. @h@ in the above example
  , rf_body :: t -- ^ Abstract refinement associated with `RTyCon`. e.g. @v > h@ in the above example
  } deriving (Eq, Generic, Data, Typeable, Functor, Foldable, Traversable)
    deriving (B.Binary, Hashable) via Generically (Ref τ t)

instance (NFData τ,   NFData t)   => NFData   (Ref τ t)

rPropP :: [(Symbol, τ)] -> r -> Ref τ (RTypeV v c tv r)
rPropP τ r = RProp τ (RHole r)

-- | @RTProp@ is a convenient alias for @Ref@ that will save a bunch of typing.
--   In general, perhaps we need not expose @Ref@ directly at all.
type RTProp c tv r = RTPropV Symbol c tv r
type RTPropV v c tv r = Ref (RTypeV v c tv ()) (RTypeV v c tv r)

type UReft r = UReftV F.Symbol r
data UReftV v r = MkUReft
  { ur_reft   :: !r
  , ur_pred   :: !(PredicateV v)
  }
  deriving (Eq, Generic, Data, Typeable, Functor, Foldable, Traversable)
  deriving (B.Binary, Hashable) via Generically (UReftV v r)

mapUReftV :: (v -> v') -> (r -> r') -> UReftV v r -> UReftV v' r'
mapUReftV f g (MkUReft r p) = MkUReft (g r) (mapPredicateV f p)

emapUReftVM
  :: Monad m
  => ([Symbol] -> v -> m v') -> (r -> m r') -> UReftV v r -> m (UReftV v' r')
emapUReftVM f g (MkUReft r p) = MkUReft <$> g r <*> emapPredicateVM f p

type BRType      = RTypeV Symbol BTyCon BTyVar    -- ^ "Bare" parsed version
type BRTypeV v   = RTypeV v BTyCon BTyVar         -- ^ "Bare" parsed version
type RRType      = RTypeV Symbol RTyCon RTyVar    -- ^ "Resolved" version
type BSort       = BRType    ()
type BSortV v    = BRTypeV v ()
type RSort       = RRType    ()
type BPVar       = PVar      BSort
type RPVar       = PVar      RSort
type RReft       = RReftV    F.Symbol
type RReftV v    = UReftV v (F.ReftV v)
type BareType    = BareTypeV F.Symbol
type BareTypeParsed = BareTypeV F.LocSymbol
type BareTypeLHName = BareTypeV LHName
type BareTypeV v = BRTypeV v (RReftV v)
type SpecType    = RRType    RReft
type SpecProp    = RRProp    RReft
type RRProp r    = Ref       RSort (RRType r)
type BRProp r    = BRPropV Symbol r
type BRPropV v r = Ref       (BSortV v) (BRTypeV v r)
type SpecRTVar   = RTVar     RTyVar RSort



type LocBareType = F.Located BareType
type LocBareTypeLHName = F.Located BareTypeLHName
type LocBareTypeParsed = F.Located BareTypeParsed
type LocSpecType = F.Located SpecType


--------------------------------------------------------------------------------
-- | Printing Refinement Types -------------------------------------------------
--------------------------------------------------------------------------------

instance Show RTyVar where
  show = F.showpp

instance F.PPrint (UReft r) => Show (UReft r) where
  show = F.showpp

instance F.PPrint (RType c tv r) => Show (RType c tv r) where
  show = F.showpp

instance F.PPrint (RTProp c tv r) => Show (RTProp c tv r) where
  show = F.showpp

instance F.PPrint BTyVar where
  pprintTidy _ (BTV α) = text (F.symbolString $ F.val α)

instance F.PPrint RTyVar where
  pprintTidy k (RTV α)
   | ppTyVar ppEnv  = F.pprintTidy k (F.symbol α) -- shows full tyvar
   | otherwise      = ppr_tyvar_short α           -- drops the unique-suffix
   where
     ppr_tyvar_short :: TyVar -> Doc
     ppr_tyvar_short = text . showPpr

instance (F.PPrint r, F.PPrint t, F.PPrint (RType c tv r)) => F.PPrint (Ref t (RType c tv r)) where
  pprintTidy k (RProp ss s) = ppRefArgs k (fst <$> ss) <+> F.pprintTidy k s

ppRefArgs :: F.Tidy -> [Symbol] -> Doc
ppRefArgs _ [] = empty
ppRefArgs k ss = text "\\" <-> hsep (ppRefSym k <$> ss ++ [F.vv Nothing]) <+> "->"

ppRefSym :: (Eq a, IsString a, F.PPrint a) => F.Tidy -> a -> Doc
ppRefSym _ "" = text "_"
ppRefSym k s  = F.pprintTidy k s

-------------------------------------------

-- Should just make this a @Pretty@ instance but its too damn tedious
-- to figure out all the constraints.

type OkRT c tv r = ( TyConable c
                   , F.PPrint tv, F.PPrint c, F.PPrint r
                   , Reftable r, Reftable (RTProp c tv ()), Reftable (RTProp c tv r)
                   , Eq c, Eq tv
                   , Hashable tv
                   )

class Reftable r => UReftable r where
  ofUReft :: UReft F.Reft -> r
  ofUReft (MkUReft r _) = ofReft r


instance UReftable (UReft F.Reft) where
   ofUReft r = r

instance UReftable () where
   ofUReft _ = mempty

class ToReftV r where
  type ReftVar r
  toReftV  :: r -> F.ReftV (ReftVar r)

instance ToReftV r => ToReftV (UReftV v r) where
  type ReftVar (UReftV v r) = ReftVar r
  toReftV = toReftV . ur_reft

instance ToReftV (F.ReftV v) where
  type ReftVar (F.ReftV v) = v
  toReftV = id

instance ToReftV () where
  type ReftVar () = Symbol
  toReftV _ = F.trueReft

class (Monoid r, F.Subable r) => Reftable r where
  isTauto :: r -> Bool
  ppTy    :: r -> Doc -> Doc

  top     :: r -> r
  top _   =  mempty

  meet    :: r -> r -> r
  meet    = mappend

  toReft  :: r -> F.Reft
  ofReft  :: F.Reft -> r

instance Semigroup F.Reft where
  (<>) = F.meetReft

instance Monoid F.Reft where
  mempty  = F.trueReft
  mappend = (<>)

instance Reftable () where
  isTauto _ = True
  ppTy _  d = d
  top  _    = ()
  meet _ _  = ()
  toReft _  = F.trueReft
  ofReft _  = ()

instance Reftable F.Reft where
  isTauto  = all F.isTautoPred . F.conjuncts . F.reftPred
  ppTy     = pprReft
  toReft   = id
  ofReft   = id
  top (F.Reft (v,_)) = F.Reft (v, F.PTrue)

instance F.Subable r => F.Subable (UReft r) where
  syms (MkUReft r p)     = F.syms r ++ F.syms p
  subst s (MkUReft r z)  = MkUReft (F.subst s r)  (F.subst s z)
  substf f (MkUReft r z) = MkUReft (F.substf f r) (F.substf f z)
  substa f (MkUReft r z) = MkUReft (F.substa f r) (F.substa f z)

instance (F.PPrint r, Reftable r) => Reftable (UReft r) where
  isTauto               = isTautoUreft
  ppTy                  = ppTyUreft
  toReft (MkUReft r ps) = toReft r `meet` toReft ps
  top (MkUReft r p)     = MkUReft (top r) (top p)
  ofReft r              = MkUReft (ofReft r) mempty

instance F.Expression (UReft ()) where
  expr = F.expr . toReft

ppTyUreft :: Reftable r => UReft r -> Doc -> Doc
ppTyUreft u@(MkUReft r p) d
  | isTautoUreft u = d
  | otherwise      = pprReft r (ppTy p d)

pprReft :: (Reftable r) => r -> Doc -> Doc
pprReft r d = braces (F.pprint v <+> colon <+> d <+> text "|" <+> F.pprint r')
  where
    r'@(F.Reft (v, _)) = toReft r

isTautoUreft :: Reftable r => UReft r -> Bool
isTautoUreft u = isTauto (ur_reft u) && isTauto (ur_pred u)

instance Reftable Predicate where
  isTauto (Pr ps)      = null ps

  ppTy r d | isTauto r      = d
           | not (ppPs ppEnv) = d
           | otherwise        = d <-> angleBrackets (F.pprint r)

  toReft (Pr ps@(p:_))        = F.Reft (parg p, F.pAnd $ pToRef <$> ps)
  toReft _                    = F.trueReft

  ofReft = todo Nothing "TODO: Predicate.ofReft"

pToRef :: PVar a -> F.Expr
pToRef p = pApp (pname p) $ F.EVar (parg p) : (thd3 <$> pargs p)

pApp      :: Symbol -> [Expr] -> Expr
pApp p es = F.mkEApp fn (F.EVar p:es)
  where
    fn    = F.dummyLoc (pappSym n)
    n     = length es

pappSym :: Show a => a -> Symbol
pappSym n  = F.symbol $ "papp" ++ show n
