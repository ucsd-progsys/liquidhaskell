{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ScopedTypeVariables        #-}

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
  , RType, RTypeV, RTypeBV (..), Ref, RefB(..), RTProp, RTPropV, RTPropBV, rPropP
  , RTyVar (..)
  , OkRT, OkRTBV

  -- * Classes describing operations on `RTypes`
  , TyConable (..)

  -- * Type Variables
  , RTVar (..), RTVInfo (..)
  , makeRTVar
  , rTVarToBind
  , setRtvPol

  -- * Predicate Variables
  , PVar
  , PVarV
  , PVarBV (PV, pname, ptype, pargs), pvType
  , Predicate
  , PredicateV
  , PredicateBV(..)
  , pappV

  -- * Expression Arguments
  , notExprArg

  -- * Manipulating `Predicates`
  , emapExprVM
  , mapPredicateV
  , emapPredicateVM
  , mapPVarV
  , emapPVarVM
  , emapSubstVM
  , pvars, pApp

  -- * Refinements
  , UReft
  , UReftV
  , UReftBV(..)
  , mapUReftV
  , emapUReftVM
  , NoReft
  , NoReftB
  , NoReftBV(..)

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
  , RPVar, RReft, RReftV, RReftBV

  -- * Printer Configuration
  , PPEnv (..)
  , ppEnv
  , ppEnvShort

  -- * Refined Function Info
  , RFInfo(..), defRFInfo, mkRFInfo, classRFInfo

  -- * Converting to and from refinements
  , ConcreteReft(..)
  , Meet(..)
  , Top(..)
  , IsReft(..)
  , isTauto
  , mapReftField
  , ofReft
  , toReft
  , toUReft
  , trueReft
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

import           Control.DeepSeq
import           Data.Traversable                       (forAccumM)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import           Data.Hashable
import qualified Data.HashMap.Strict                    as M
import qualified Data.List                              as L
import           Data.Maybe                             (mapMaybe)
import           Data.List                              as L (nub)
import qualified Data.HashSet                           as S
import           Text.PrettyPrint.HughesPJ              hiding (first, (<>))
import           Language.Fixpoint.Misc

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Expr, ExprBV(..), KVarSubst, Symbol)

import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.UX.Config


newtype RFInfo = RFInfo {permitTC :: Maybe Bool }
  deriving (Generic, Data, Show, Eq)

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
  } deriving (Generic, Data, Show)

instance F.Loc TyConP where
  srcSpan tc = F.SS (tcpLoc tc) (tcpLoc tc)

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
  deriving (Data, Generic, Eq, Functor, Foldable, Show, Traversable)
  deriving (B.Binary, Hashable) via Generically (SizeFunV v)

instance NFData v => NFData (SizeFunV v)

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
type PVarV v t = PVarBV Symbol v t

-- | A predicate variable with arguments, e.g. @p :: x:a -> z:a -> Bool@.
--
-- A 'PVarBV' appears in two roles:
--
-- 1. As a __binder__ inside 'RAllP', declaring the predicate variable and its
--    signature.  Here each @pargs@ entry has the form @(t, x, EVar x)@: the
--    expression is the canonical variable itself (identity).
--
-- 2. As a __use site__ inside 'ur_pred' of a 'UReftBV' (as 'UsedPVarBV'),
--    recording which abstract refinement is applied and with which actual
--    argument expressions.
--
-- Example: given
--
-- @{-\@ foo :: forall a \<p :: x:a -> z:a -> Bool\>. y:a -> a\<p y\> \@-}@
--
-- * At the __binder__ (inside 'RAllP'):
--   @PV{pname="p", ptype=a, pargs=[(a, "x", EVar "x")]}@
-- * At the __use site__ @a\<p y\>@ (inside 'ur_pred'):
--   @PV{pname="p", ptype=a, pargs=[(a, "x", EVar "y")]}@
--
-- * @pname@ is the name of the predicate variable, e.g. @p@
-- * @ptype@ is the type of the last (value) argument, i.e. the type being
--   constrained, e.g. @a@
-- * @pargs@ is the list of non-value arguments (excluding the last one).
--   Each triple is @(type, formal-binder, actual-expr)@.
--   The __formal-binder__ always comes from the predicate declaration site
--   (preserved by 'txPvar'); the __actual-expr__ is updated at each call site.
--
--   The expressions in @pargs@ are the __actual arguments__ at each use site.
--   In 'meetListWithPSub' (abstract refinement subtyping), if all expressions
--   equal their formal binders (@\(_, x, EVar y) -> x == y@) no substitution
--   is needed; otherwise the substitution @[(formal, actual), ...]@ built from
--   @pargs@ is applied to the concrete predicate body.
--
data PVarBV b v t = PV
  { pname :: !b
  , ptype :: !t
  , pargs :: ![(t, b, F.ExprBV b v)]
  } deriving (Generic, Data, Show, Functor)
  deriving B.Binary via Generically (PVarBV b v t)

mapPVarV :: (v -> v') -> (t -> t') -> PVarBV b v t -> PVarBV b v' t'
mapPVarV f g PV {..} =
    PV
      { ptype = g ptype
      , pargs = [ (g t, s, fmap f e) | (t, s, e) <- pargs ]
      , ..
      }

-- | A map traversal that collects the local variables in scope
emapPVarVM :: (Monad m, Hashable b) => ([b] -> v -> m v') -> ([b] -> t -> m t') -> PVarBV b v t -> m (PVarBV b v' t')
emapPVarVM f g pv = do
    ptype <- g (argSyms (pargs pv)) (ptype pv)
    (_, pargs) <- forAccumM [] (pargs pv) $ \ss (t, s, e) -> do
      (s:ss,) <$> ((,,) <$> g (s:ss) t <*> pure s <*> emapExprVM (f . ((s:ss) ++)) e)
    return pv{ptype, pargs}
  where
    argSyms = map (\(_, s, _) -> s)

instance Eq b => Eq (PVarBV b v t) where
  pv == pv' = pname pv == pname pv' {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord b => Ord (PVarBV b v t) where
  compare (PV n _ _)  (PV n' _ _) = compare n n'

instance (NFData b, NFData v, NFData t) => NFData (PVarBV b v t)

instance Hashable b => Hashable (PVarBV b v a) where
  hashWithSalt i (PV n _ _) = hashWithSalt i n

pvType :: PVarBV b v t -> t
pvType = ptype

instance (Ord b, F.Fixpoint b, Hashable b, F.PPrint b, Ord v, F.Fixpoint v, F.PPrint v) => F.PPrint (PVarBV b v a) where
  pprintTidy _ = pprPvar

pprPvar :: (Ord b, F.Fixpoint b, Hashable b, F.PPrint b, Ord v, F.Fixpoint v, F.PPrint v) => PVarBV b v a -> Doc
pprPvar (PV s _ xts) = F.pprint s <+> hsep (F.pprint . thd3 <$> xts)

-- | A map traversal that collects the local variables in scope
emapExprVM :: (Monad m, Hashable b) => ([b] -> v -> m v') -> ExprBV b v -> m (ExprBV b v')
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
      PKVar k tsu su -> PKVar k tsu <$> emapSubstVM (f . (domain su ++) . (acc ++)) su
      PAll bnds e -> PAll bnds <$> go (map fst bnds ++ acc) e
      PExist bnds e -> PExist bnds <$> go (map fst bnds ++ acc) e
      ECoerc srt0 srt1 e -> ECoerc srt0 srt1 <$> go acc e
      ELet x e1 e2 -> ELet x <$> go acc e1 <*> go (x:acc) e2

    domain m = M.keys $ F.fromKVarSubst m

emapSubstVM :: (Monad m, Hashable b) => ([b] -> v -> m v') -> KVarSubst b v -> m (KVarSubst b v')
emapSubstVM f m = F.toKVarSubst . M.fromList <$> mapM (traverse (emapExprVM f)) (M.toList $ F.fromKVarSubst m)

--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

type UsedPVar    = UsedPVarV Symbol
type UsedPVarV v = UsedPVarBV Symbol v
type UsedPVarBV b v = PVarBV b v (NoReftBV b v)

type Predicate = PredicateV Symbol
type PredicateV v = PredicateBV Symbol v
newtype PredicateBV b v = Pr [UsedPVarBV b v]
  deriving (Generic, Data, Show)
  deriving (B.Binary, Hashable) via Generically (PredicateBV b v)

mapPredicateV :: (v -> v') -> PredicateV v -> PredicateV v'
mapPredicateV f (Pr xs) = Pr (map (mapPVarV f (const NoReft)) xs)

-- | A map traversal that collects the local variables in scope
emapPredicateVM :: Monad m => ([Symbol] -> v -> m v') -> PredicateV v -> m (PredicateV v')
emapPredicateVM f (Pr xs) = Pr <$> mapM (emapPVarVM f (\_ _ -> pure NoReft)) xs

instance (Ord b, Ord v) => Eq (PredicateBV b v) where
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

instance Eq b => Semigroup (PredicateBV b v) where
  p <> p' = pdAnd [p, p']

instance (Ord b, F.Fixpoint b, Hashable b, F.PPrint b, Ord v, F.Fixpoint v, F.PPrint v) => F.PPrint (PredicateBV b v) where
  pprintTidy _ (Pr [])  = text "True"
  pprintTidy k (Pr pvs) = hsep $ punctuate (text "&") (F.pprintTidy k <$> pvs)

instance (Semigroup (F.ReftBV b v), Eq b) => Semigroup (UReftBV b v) where
  MkUReft x y <> MkUReft x' y' = MkUReft (x <> x') (y <> y')

instance Monoid UReft where
  mempty  = MkUReft mempty mempty
  mappend = (<>)


pdTrue :: PredicateBV b v
pdTrue         = Pr []

pdAnd :: (Foldable t, Eq b) => t (PredicateBV b v) -> PredicateBV b v
pdAnd ps       = Pr (nub $ concatMap pvars ps)

pvars :: PredicateBV b v -> [UsedPVarBV b v]
pvars (Pr pvs) = pvs

instance (Hashable v, F.Refreshable v) => F.Subable (UsedPVarBV v v) where
  type Variable (UsedPVarBV v v) = v
  syms pv = F.syms [ e | (_, _x, e) <- pargs pv ]
  substr ns s pv = pv { pargs = mapThd3 (F.substr ns s) <$> pargs pv }


instance (Hashable v, F.Refreshable v) => F.Subable (PredicateBV v v) where
  type Variable (PredicateBV v v) = v
  syms (Pr pvs) = F.syms pvs
  substr ns s (Pr pvs) = Pr (F.substr ns s <$> pvs)

instance NFData UReft

newtype BTyVar = BTV F.LocSymbol
  deriving (Show, Generic, Data)
  deriving (B.Binary, Hashable) via Generically BTyVar

newtype RTyVar = RTV TyVar deriving (Generic, Data, Show)

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

instance CompatibleBinder (F.Located Symbol) BTyVar where
  coerceBinder (BTV tv) = tv

instance CompatibleBinder Symbol BTyVar where
  coerceBinder tv = coerceBinder (coerceBinder tv :: F.Located Symbol)

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
  deriving (Generic, Data, Show)
  deriving (B.Binary, Hashable) via Generically BTyCon

data RTyCon = RTyCon
  { rtc_tc    :: TyCon         -- ^ GHC Type Constructor
  , rtc_pvars :: ![RPVar]      -- ^ Predicate Parameters
  , rtc_info  :: !TyConInfo    -- ^ TyConInfo
  }
  deriving (Generic, Data, Show)

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

instance F.PPrint v => F.PPrint (RTVar b v c v) where
  pprintTidy k (RTVar x _) = F.pprintTidy k x

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
  } deriving (Generic, Data, Show)

instance NFData TyConInfo

--------------------------------------------------------------------------------
-- | Unified Representation of Refinement Types --------------------------------
--------------------------------------------------------------------------------

type RTVU c tv = RTVUV Symbol c tv
type RTVUV v c tv = RTVUBV Symbol v c tv
type RTVUBV b v c tv = RTVar b v c tv
type PVU c tv = PVUV Symbol c tv
type PVUV v c tv = PVarV v (RTypeV v c tv NoReft)
type PVUBV b v c tv = PVarBV b v (RTypeBV b v c tv (NoReftBV b v))

type RType c tv r = RTypeV Symbol c tv r
type RTypeV v c tv = RTypeBV Symbol v c tv

-- | A refinement type
--
-- * @b@ is the type of bindings
-- * @v@ is the type of variables appearing in expressions
-- * @c@ is the type of type constructors
-- * @tv@ is the type of type variables
-- * @r@ is the type of refinements. Must instance the 'IsReft' class. There are
--   only three instances of 'IsReft': 'ReftBV', 'NoReftBV', and 'UReftBV'.
--
-- A refinement might be missing (e.g. @r@ is @NoReft@), if the RTypeBV is used to
-- represent the type of an entity that can't use refinements, e.g. the type of
-- an abstract predicate.
data RTypeBV b v c tv r
  =
    -- | A type variable, e.g. @a@ in @a -> a@
    --
    -- When the refinement is @(v, e)@, the constructor represents @{v:a | e}@.
    --
    -- The scope of @v@ is the expression @e@ and the type @a@.
    --
    -- * @rt_var@ is the type variable, e.g. @a@
    -- * @rt_reft@ is the refinement, e.g. @(v, v > 0)@ in @{v:a | v > 0}@
    --
    RVar {
      rt_var    :: !tv
    , rt_reft   :: !r
    }

    -- | A function type, e.g. @x:a -> y:{y1:a | x = y1} -> {v:a | y == v}@
    --
    -- * @rt_bind@ is the binder of the first argument, e.g. @x@ in the above
    --   example. The scope of @rt_bind@ is @rt_in@ and @rt_out@. Note, however,
    --   that @rt_bind@ is not used in @rt_in@ after a SpecType is constructed.
    --   This is because all the occurrences of the binder are switched to the
    --   name of the binder in the refinement type of @rt_in@ (e.g.
    --   @{y:{y1:a | x = y} -> ...}@ is changed to @{y:{y1:a | x = y1} -> ...}@).
    --   This transformation is performed by @rebind@ in @ofBRType@.
    --
    -- * @rt_rinfo@ controls whether typeclass method elaboration is permitted
    --   on this arrow. @RFInfo (Just True)@ means typeclass arguments are
    --   allowed; @RFInfo Nothing@ is the default for user-written types.
    --
    -- * @rt_in@ is the type of the first argument, e.g. @a@
    --
    -- * @rt_out@ is the type of the result, e.g.
    --   @y:{y1:a | x = y1} -> {v:a | y == v}@
    --
    -- * @rt_reft@ is the refinement of the function type. If the refinement is
    --   @(v0, e)@, then the represented type is
    --   @{v0: (x:a -> y:{y1:a | x = y1} -> {v:a | y == v}) | e}@.
    --
    --   The scope of @v0@ is the entire function type and @e@, i.e.
    --   @x:a -> y:{y1:a | x = y1} -> {v:a | y == v}@.
    --
  | RFun  {
      rt_bind   :: !b
    , rt_rinfo  :: !RFInfo
    , rt_in     :: !(RTypeBV b v c tv r)
    , rt_out    :: !(RTypeBV b v c tv r)
    , rt_reft   :: !r
    }

    -- | A universally quantified type, e.g. @forall (a :: k). a -> a@
    --
    -- * @rt_tvbind@ is the type variable and its kind, e.g. @a :: k@ in the
    --   above example. If @rtv_is_val@ is True in the variable's info, the
    --   type variable also introduces an expression-level binder (a "value
    --   type variable") with name @rtv_name@ and kind @rtv_kind@.
    --
    -- * @rt_ty@ is the body of the quantified type, e.g. @a -> a@
    --
    -- * @rt_ref@ is the refinement of the quantified type.
    --   If the refinement is @(v, e)@, then the represented type is
    --   @{v: (forall (a :: k). a -> a) | e}@.
    --
    --   The scope of @v@ is the entire quantified type and @e@.
    --
  | RAllT {
      rt_tvbind :: !(RTVUBV b v c tv)
    , rt_ty     :: !(RTypeBV b v c tv r)
    , rt_ref    :: !r
    }

    -- | A universally quantified type over predicate variables, e.g.
    --  @forall \<p :: Int -> Bool\>. {v:Int | p v} -> Int@
    --
    -- * @rt_pvbind@ is the predicate variable and its type, e.g.
    --   @p :: Int -> Bool@ in the above example. See 'PVarBV' for details on
    --   how predicate variable arguments are stored.
    --
    -- * @rt_ty@ is the body of the quantified type, e.g.
    --   @{v:Int | p v} -> Int@. The predicate variable @rt_pvbind@ is in scope
    --   in @rt_ty@ and can be applied to type constructors via @rt_pargs@ in
    --   'RApp'.
    --
  | RAllP {
      rt_pvbind :: !(PVUBV b v c tv)
    , rt_ty     :: !(RTypeBV b v c tv r)
    }

    -- | Application of a type constructor, e.g. @{v:[a]\<{\\h v -> v > h}\> | len v > 0}@
    --
    -- * @rt_tycon@ is the type constructor, e.g. @[]@
    --
    -- * @rt_args@ is the list of type arguments, e.g. the singleton list
    --   containing the type @a@
    --
    -- * @rt_pargs@ is the list of predicate arguments, e.g. the singleton list
    --   containing the predicate value @RProp [("h",_)] (RHole {v > h})@.
    --   These are the abstract refinements supplied inside @\<...\>@.
    --
    -- * @rt_reft@ is the refinement of the type application.
    --   If the refinement is @(v, e)@, then the represented type is
    --   @{v: [a]\<{\\h v -> v > h}\> | e}@, e.g. @(v, len v > 0)@.
    --
    --   The scope of @v@ is the entire type application and @e@.
    --
    -- Invariant: the types in the predicates of @rt_pargs@ must match the types
    -- of the predicates that @rt_tycon@ expects when applied to @rt_args@.
    -- This invariant is loosely maintained when processing @RApp@. It is not
    -- trivial to enforce at construction time (e.g. with a smart constructor)
    -- becase the expected types are not available in the arguments of @RApp@.
    --
  | RApp  {
      rt_tycon  :: !c
    , rt_args   :: ![RTypeBV b v c tv r]
    , rt_pargs  :: ![RTPropBV b v c tv r]
    , rt_reft   :: !r
    }

    -- | Existential quantification over an expression variable.
    -- Printed as @exists [x:T]. TYPE@.
    --
    -- @REx@ is introduced by A-normalisation ('addExist' in @Bare/Expand.hs@)
    -- when an abstract refinement is applied to a complex (non-variable)
    -- expression.  A fresh ghost variable is created to name the expression so
    -- that the fixpoint solver can reason about it without duplicating it.
    -- See @tests/pos/TestREx.hs@ for an actual test.
    --
    -- Example: the return type @a\<p (i+1)\>@ of
    --
    -- > assume next :: forall a <p :: Int -> a -> Bool>. i:Int -> a<p i> -> a<p (i+1)>
    --
    -- is A-normalised to:
    --
    -- @REx "ex#0" {v:Int | v == i+1} (RApp a [] [RProp [("ex#0",_)] (a<p ex#0>)] _)@
    --
    -- * @rt_bind@ is the ghost binder, e.g. @ex#0@ above.
    --   Its scope is @rt_ty@.
    -- * @rt_exarg@ is the type of the ghost variable, e.g.
    --   @{v:Int | v == i+1}@ — a singleton type pinning the ghost to the
    --   original expression.
    -- * @rt_ty@ is the body type, e.g. @a\<p ex#0\>@, which now mentions the
    --   ghost instead of the original complex expression.
    --
    -- Semantics: when checking @REx x tx t \<: t2@, a fresh name @y@ is
    -- generated, @y:tx@ is added to the environment, and @t[x:=y] \<: t2@ is
    -- checked. On the RHS, @t1 \<: REx x tx t2@ is handled symmetrically.
    --
  | REx {
      rt_bind   :: !b
    , rt_exarg  :: !(RTypeBV b v c tv r)
    , rt_ty     :: !(RTypeBV b v c tv r)
    }

    -- | An expression argument to a type alias (not a proper type).
    --
    -- Example: given @{-\@ type VectorN a N = {v:[a] | len v == N} \@-}@,
    -- the usage @VectorN Int 3@ is represented as:
    -- @RApp VectorN [RApp Int ..., RExprArg (ECon (I 3))] [] _@
    --
    -- The @RExprArg@ appears in the @rt_args@ list of 'RApp' in position
    -- corresponding to the expression parameter @N@.
    --
    -- Parsed from: bare numeric literals (e.g. @3@), or expressions in braces
    -- @{expr}@ or parentheses @(expr)@ at type-argument positions.
    --
  | RExprArg (F.Located (ExprBV b v))

    -- | Type-level application that is /not/ a saturated type constructor
    -- application, e.g. @f a@ where @f@ is a type variable of higher kind.
    --
    -- Example: in @forall (f :: * -> *) a. f a -> f a@,
    -- the @f a@ part is:
    -- @RAppTy (RVar f (v, True)) (RVar a (v, True)) (v, True)@
    --
    -- * @rt_arg@ is the type being applied, e.g. @RVar f _@
    -- * @rt_res@ is the type argument, e.g. @RVar a _@
    -- * @rt_reft@ is the refinement of the application result.
    --   If the refinement is @(v, e)@, then the represented type is
    --   @{v: f a | e}@.
    --
    --   The scope of @v@ is the entire type application and @e@.
    --
  | RAppTy{
      rt_arg   :: !(RTypeBV b v c tv r)
    , rt_res   :: !(RTypeBV b v c tv r)
    , rt_reft  :: !r
    }

    -- | A type annotated with a verification obligation (constraint, invariant,
    -- or termination metric). It wraps an actual type @rt_ty@ with auxiliary
    -- information for constraint generation.
    --
    -- For the invariant and termination obligations, the wrapping is done after
    -- parsing. In the case of termination, it is done in constraint generation
    -- and depends on the part of the code for which constraints are being
    -- generated. That is, different locations of the code have available different
    -- variations of the type representation.
    --
    -- === Example (OCons)
    --
    -- The type
    --
    -- > {x:Int |- {v:Int | v > 0} \<: {v:Int | v > x}} => Int -> Int
    --
    -- is represented as:
    --
    -- > RRTy
    -- >   [("x", Int), (dummySymbol, {v:Int | v > 0}), (dummySymbol, {v:Int | v > x})]
    -- >   trueReft
    -- >   OCons
    -- >   (Int -> Int)
    --
    -- === Example (OInv)
    --
    -- Given
    --
    -- >  {-@ invariant {v:Peano | toInt v >= 0} @-}
    -- >  {-@ add :: Peano -> Peano -> Peano @-}
    --
    -- the invariant obligation generated for @add@ is represented as:
    --
    -- >  RFun "lq1"                                    -- first arg binder
    -- >      defRFInfo
    -- >      (RApp Peano [] [] trueReft)              -- Peano (first arg type)
    -- >      (RFun "lq2"                              -- second arg binder
    -- >           defRFInfo
    -- >           (RApp Peano [] [] trueReft)         -- Peano (second arg type)
    -- >           (RRTy                               -- ← invariant obligation wraps the RESULT
    -- >               [("xInv", RApp Peano [] [] trueReft)]   -- rt_env: bind scrutinee
    -- >               (MkUReft                                -- rt_ref: NON-TRIVIAL
    -- >                  (Reft ("v",                          --   binder "v" is bound HERE in the Reft
    -- >                         PIff (EVar "v")              --   v ⟺ (toInt xInv >= 0)[xInv/v]
    -- >                              (PAtom Ge (EApp "toInt" (EVar "xInv"))
    -- >                                        (ECon (I 0)))))
    -- >                  (Pr []))
    -- >               OInv                                    -- rt_obl: invariant
    -- >               (RApp Peano [] [] trueReft))            -- rt_ty: actual result type
    -- >           trueReft)
    -- >      trueReft
    --
    -- === Example (OTerm)
    --
    -- Given
    --
    -- > {-@ fib :: n:Nat -> Nat / [n] @-}
    -- > fib :: Int -> Int
    -- > fib 0 = 0
    -- > fib 1 = 1
    -- > fib n = fib (n - 1) + fib (n - 2)
    --
    -- The type represenation available when checking the recursive calls is:
    --
    -- >  RFun "n"                                       -- binder for the argument
    -- >       defRFInfo
    -- >       (RApp Int [] []                           -- Nat = {v:Int | v >= 0}
    -- >             (MkUReft (Reft ("v", PAtom Ge (EVar "v") (ECon (I 0)))) (Pr [])))
    -- >       (RRTy                                    -- ← termination obligation wraps RESULT
    -- >           []                                          -- rt_env: empty
    -- >           (MkUReft                                    -- rt_ref: NON-TRIVIAL
    -- >              (Reft ("vvRec",                          --   "vvRec" bound HERE in the Reft
    -- >                     PIff (EVar "vvRec")               --   vvRec ⟺ (n' < n ∧ n' >= 0)
    -- >                          (PAnd [ PAtom Lt (EVar "n'") (EVar "n")
    -- >                                , PAtom Ge (EVar "n'") (ECon (I 0))
    -- >                                ])))
    -- >              (Pr []))
    -- >           OTerm                                       -- rt_obl: termination
    -- >           (RApp Int [] []                             -- rt_ty: actual result type (Nat)
    -- >                 (MkUReft (Reft ("v", PAtom Ge (EVar "v") (ECon (I 0)))) (Pr []))))
    -- >       trueReft
    --
    -- The binding @n'@ is instantiated at different places with the argument of
    -- the recursive call, e.g. @n - 1@ and @n - 2@.
    --
    -- === Fields
    --
    -- * @rt_env@ is the typing environment and subtyping pair. For @OCons@,
    --   the last two entries are the LHS and RHS of the subtyping obligation;
    --   preceding entries form the local typing environment. For @OTerm@ the
    --   environment is empty, and for @OInv@ it contains a single binding.
    --
    -- * @rt_ref@ is the refinement predicate (for @OInv@ and @OTerm@ this
    --   carries the invariant or termination metric). For @OCon@s, this is always
    --   @trueReft@, akin to leaving the field unused. For @OInv@, the
    --   refinement is an encoding of the invariant predicate, and for @OTerm@
    --   it contains the termination constraint (the metric on the argument of
    --   the recursive call must be non-negative and smaller than the metric on
    --   the initial argument.
    --
    -- * @rt_obl@ is the kind of obligation:
    --   - @OCons@: subtyping constraint, parsed from
    --     @{env |- t1 \<: t2} => TYPE@
    --   - @OInv@: data-type invariant, generated by 'addInvCond'
    --   - @OTerm@: termination metric, generated by 'addObligation'
    -- * @rt_ty@ is the underlying actual type, e.g. @Int -> Int@
    --
    -- In all cases, the obligation is discharged as a side-effect during
    -- constraint generation, and @rt_ty@ is the type used for further checking.
    --
    -- Unlike in other data constructors of @RTypeBV@, the bind of @rt_ref@
    -- does not scope over other fields. As can be seen in the example of @OInv@,
    -- @rt_env@ binds scope over @rt_ref@.
    --
  | RRTy  {
      rt_env   :: ![(b, RTypeBV b v c tv r)]
    , rt_ref   :: !r
    , rt_obl   :: !Oblig
    , rt_ty    :: !(RTypeBV b v c tv r)
    }

    -- | A hole: a placeholder that instructs LH to infer the type by matching
    -- against the Haskell type and inserting k-variables for inference.
    --
    -- Example: @{-\@ f :: x:_ -> {v:_ | v > x} \@-}@ contains two holes.
    -- Each @_@ becomes @RHole r@ where @r@ is either a @true@ refinement or a
    -- user-supplied refinement (e.g. @v > x@ in the second hole).
    --
    -- During elaboration, holes are replaced with actual types from GHC's type
    -- checker, with fresh k-variables for the refinements.
    -- See: tests/pos/Holes.hs
    --
  | RHole r
  deriving (Eq, Generic, Data, Functor, Foldable, Show, Traversable)
  deriving (B.Binary, Hashable) via Generically (RTypeBV b v c tv r)

instance (NFData b, NFData v, NFData c, NFData tv, NFData r) => NFData (RTypeBV b v c tv r)

makeRTVar :: tv -> RTVar b v c tv
makeRTVar a = RTVar a (RTVNoInfo True)

notExprArg :: RTypeV v c tv r -> Bool
notExprArg (RExprArg _) = False
notExprArg _            = True

instance (Eq tv) => Eq (RTVar b v c tv) where
  t1 == t2 = ty_var_value t1 == ty_var_value t2

-- | @RTVar@ is the type of type variables in the refinement type system. It
-- contains a type variable, optionally a kind, and information about how to
-- instantiate it (polymorphic vs. monomorphic refinements).
data RTVar b v c tv = RTVar
  { ty_var_value :: tv
  , ty_var_info  :: RTVInfo b v c tv
  } deriving (Generic, Data, Show)
    deriving (B.Binary, Hashable) via Generically (RTVar b v c tv)

data RTVInfo b v c tv
  = RTVNoInfo { rtv_is_pol :: Bool }
  | RTVInfo { rtv_name   :: b
            , rtv_kind   :: RTypeBV b v c tv (NoReftBV b v)
            , rtv_is_val :: Bool
            , rtv_is_pol :: Bool -- true iff the type variable gets instantiated with
                                 -- any refinement (ie is polymorphic on refinements),
                                 -- false iff instantiation is with true refinement
            } deriving (Generic, Data, Eq, Show)
              deriving (B.Binary, Hashable) via Generically (RTVInfo b v c tv)


setRtvPol :: RTVar b v c tv -> Bool -> RTVar b v c tv
setRtvPol (RTVar a i) b = RTVar a (i{rtv_is_pol = b})

rTVarToBind :: RTVar b v c tv -> Maybe (b, RTypeBV b v c tv (NoReftBV b v))
rTVarToBind = go . ty_var_info
  where
    go RTVInfo{..} | rtv_is_val = Just (rtv_name, rtv_kind)
    go _                        = Nothing

instance (NFData b, NFData v, NFData c, NFData tv) => NFData   (RTVar b v c tv)
instance (NFData b, NFData v, NFData c, NFData tv) => NFData   (RTVInfo b v c tv)

type Ref τ t = RefB Symbol τ t

-- | @Ref@ describes `Prop τ` and `HProp` arguments applied to type constructors.
--   For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
--   * the `RProp`  denoted by `{\h -> v > h}` to
--   * the `RTyCon` denoted by `[]`.
--   Thus, @Ref@ is used for abstract-predicate (arguments) that are associated
--   with _type constructors_ i.e. whose semantics are _dependent upon_ the data-type.
--   In contrast, the `Predicate` argument in `ur_pred` in the @UReft@ applies
--   directly to any type and has semantics _independent of_ the data-type.

data RefB b τ t = RProp
  { rf_args :: [(b, τ)] -- ^ arguments. e.g. @h@ in the above example
  , rf_body :: t -- ^ Abstract refinement associated with `RTyCon`. e.g. @v > h@ in the above example
  } deriving (Eq, Generic, Data, Functor, Foldable, Show, Traversable)
    deriving (B.Binary, Hashable) via Generically (RefB b τ t)

instance (NFData b, NFData τ, NFData t) => NFData (RefB b τ t)

rPropP :: [(b, τ)] -> r -> RefB b τ (RTypeV v c tv r)
rPropP τ r = RProp τ (RHole r)

-- | @RTProp@ is a convenient alias for @Ref@ that will save a bunch of typing.
--   In general, perhaps we need not expose @Ref@ directly at all.
type RTProp c tv r = RTPropV Symbol c tv r
type RTPropV v c tv r = RTPropBV Symbol v c tv r
type RTPropBV b v c tv r = RefB b (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv r)

type UReft = UReftV F.Symbol
type UReftV v = UReftBV F.Symbol v

-- | A combined refinement carrying both a first-order predicate and a
-- conjunction of abstract-refinement (predicate-variable) applications.
-- This is the @r@ parameter of 'RTypeBV' in fully-elaborated types:
-- @SpecType = 'RRType' RReft@ where @RReft = UReft F.Reft =
-- UReftBV Symbol Symbol F.Reft@.
--
-- Example: the type @Int\<p m\>@ where @p :: x:Int -> z:Int -> Bool@ is an
-- abstract refinement quantified by an enclosing 'RAllP', applied with
-- extra argument @m@, is represented as:
--
-- @
-- MkUReft
--   { ur_reft = F.Reft ("VV", PTrue)          -- no first-order constraint
--   , ur_pred = Pr [ PV { pname = "p"
--                       , ptype = intSort
--                       , pargs = [(intSort, "x", EVar "m")] } ]
--   }
-- @
--
-- If the type also carries a first-order constraint, e.g. a type alias that
-- expands to @{VV:Int | VV > 0}@ combined with an abstract refinement, then
-- @ur_reft@ would be @F.Reft ("VV", VV > 0)@ alongside the non-empty @ur_pred@.
--
-- * @ur_reft@ is the first-order part of the refinement, stored as a fixpoint
--   'F.Reft' @(binder, predicate)@.  The standard value-variable is @"VV"@
--   (fixpoint's canonical binder, normalised from the user's @v@ choice).
-- * @ur_pred@ is the abstract-refinement part: a 'PredicateBV' (= @Pr [UsedPVarBV]@),
--   i.e. a conjunction of predicate-variable applications.
--   Each 'UsedPVarBV' records which predicate variable is used (via @pname@),
--   and the actual argument expressions (@pargs@) at this use site (see 'PVarBV').
--
-- During constraint generation, @ur_pred@ is eliminated by
-- 'replacePredsWithRefs': each predicate-variable application is converted
-- to an uninterpreted function call @papp_n(p, VV, e1, ..., en)@ via
-- 'pVartoRConc' (using the @ur_reft@ binder @VV@) and
-- conjoined into @ur_reft@, producing a pure 'F.Reft' understood by the SMT
-- solver.  After this step, @ur_pred@ becomes @Pr []@.
--
-- 'toReft' on a 'UReftBV' discards @ur_pred@ entirely and returns only
-- @ur_reft@; it must therefore be called only after predicate-replacement.
--
data UReftBV b v = MkUReft
  { ur_reft   :: !(F.ReftBV b v)
  , ur_pred   :: !(PredicateBV b v)
  }
  deriving (Eq, Generic, Data)
  deriving (B.Binary, Hashable) via Generically (UReftBV b v)

deriving instance (Show (F.ReftBV b v), Show (PredicateBV b v)) => Show (UReftBV b v)

mapUReftV :: (v -> v') -> (F.ReftV v -> F.ReftV v') -> UReftV v -> UReftV v'
mapUReftV f g (MkUReft r p) = MkUReft (g r) (mapPredicateV f p)

emapUReftVM
  :: Monad m
  => ([Symbol] -> v -> m v') -> (F.ReftV v -> m (F.ReftV v')) -> UReftV v -> m (UReftV v')
emapUReftVM f g (MkUReft r p) = MkUReft <$> g r <*> emapPredicateVM f p

type role NoReftBV phantom phantom
type NoReft = NoReftB Symbol
type NoReftB b = NoReftBV b Symbol
data NoReftBV b v = NoReft
  deriving (Eq, Generic, Data, Functor, Foldable, Show, Traversable)
  deriving (B.Binary, Hashable) via Generically (NoReftBV b v)

instance NFData (NoReftBV b v)

instance F.PPrint (NoReftBV b v) where
  pprintTidy _ _ = text $ show ()

instance Hashable b => F.Subable (NoReftBV b v) where
  type Variable (NoReftBV b v) = b
  syms _   = S.empty
  substr _ _  = id

instance Semigroup (NoReftBV b v) where
  _ <> _ = NoReft

instance Monoid (NoReftBV b v) where
  mempty = NoReft

type BRType      = RTypeV Symbol BTyCon BTyVar    -- ^ "Bare" parsed version
type BRTypeV v   = RTypeV v      BTyCon BTyVar    -- ^ "Bare" parsed version
type RRType      = RTypeV Symbol RTyCon RTyVar    -- ^ "Resolved" version
type BSort       = BRType    NoReft
type BSortV v    = BRTypeV v (NoReftBV Symbol v)
type RSort       = RRType    NoReft
type BPVar       = PVar      BSort
type RPVar       = PVar      RSort
type RReft       = RReftV    F.Symbol
type RReftV v    = RReftBV Symbol v
type RReftBV b v = UReftBV b v
type BareType    = BareTypeV F.Symbol
type BareTypeParsed = BareTypeV F.LocSymbol
type BareTypeLHName = BareTypeV LHName
type BareTypeV v = BRTypeV v (RReftV v)
type SpecType    = RRType    RReft
type SpecProp    = RRProp    RReft
type RRProp r    = Ref       RSort (RRType r)
type BRProp r    = BRPropV Symbol r
type BRPropV v r = Ref       (BSortV v) (BRTypeV v r)
type SpecRTVar   = RTVar Symbol Symbol RTyCon RTyVar



type LocBareType = F.Located BareType
type LocBareTypeLHName = F.Located BareTypeLHName
type LocBareTypeParsed = F.Located BareTypeParsed
type LocSpecType = F.Located SpecType


--------------------------------------------------------------------------------
-- | Printing Refinement Types -------------------------------------------------
--------------------------------------------------------------------------------

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

type OkRT c tv r =
  ( TyConable c
  , F.PPrint tv, F.PPrint c, F.PPrint r, F.PPrint (ReftVar r)
  , F.Fixpoint (ReftVar r)
  , IsReft r
  , ReftBind r ~ F.Symbol
  , Eq c, Eq tv, Ord (ReftVar r)
  , Hashable tv
  )

type OkRTBV b v c tv r =
  ( TyConable c
  , F.PPrint b, F.PPrint v, F.PPrint tv, F.PPrint c, F.PPrint r, F.PPrint (ReftVar r)
  , F.Fixpoint b, F.Fixpoint v, F.Fixpoint (ReftVar r)
  , F.Binder b
  , IsReft r
  , ReftBind r ~ b
  , v ~ F.Symbol
  , Eq c, Eq tv, Ord b, Ord v, Ord (ReftVar r)
  , Hashable tv
  )

-- | Types that can be combined conjunctively in some sense
class Semigroup r => Meet r where
  meet :: r -> r -> r
  meet = (<>)

-- | Types whose refinements can be cleared to true
class Top r where
  top :: r -> r

-- | The universe of refinement types that can be used in RTypes.
data ConcreteReft r b v where
  ConcreteNoReft :: ConcreteReft (NoReftBV b v) b v
  ConcreteReft :: F.ReftBV b v -> ConcreteReft (F.ReftBV b v) b v
  ConcreteUReft :: UReftBV b v -> ConcreteReft (UReftBV b v) b v

-- | Types that can be constructed from a 'F.ReftBV'.
--
-- Only three types can be 'IsReft': 'NoReftBV', 'F.ReftBV', and 'UReftBV'.
--
-- 'ofConcreteReft' and 'toConcreteReft' must be inverses of each other.
--
-- In order to allow distinguishing the @r@ type when no value is present
-- (e.g. in @ofReft@ or @trueReft@), 'toConcreteReft' must be non-strict.
--
class (F.Binder (ReftBind r), Top r) => IsReft r where
  type ReftVar r
  type ReftBind r
  ofConcreteReft :: ConcreteReft r (ReftBind r) (ReftVar r) -> r
  toConcreteReft :: r -> ConcreteReft r (ReftBind r) (ReftVar r)

ofReft :: forall r. IsReft r => F.ReftBV (ReftBind r) (ReftVar r) -> r
ofReft r = case toConcreteReft @r (error "ofReft") of
  ConcreteNoReft -> NoReft
  ConcreteReft _ -> r
  ConcreteUReft _ -> MkUReft r pdTrue

toReft :: IsReft r => r -> F.ReftBV (ReftBind r) (ReftVar r)
toReft r0 = case toConcreteReft r0 of
   ConcreteNoReft -> F.trueReft
   ConcreteReft r -> r
   ConcreteUReft (MkUReft r _) -> r

toUReft :: IsReft r => r -> UReftBV (ReftBind r) (ReftVar r)
toUReft r0 = case toConcreteReft r0 of
   ConcreteNoReft -> MkUReft F.trueReft pdTrue
   ConcreteReft r -> MkUReft r pdTrue
   ConcreteUReft r -> r

instance Top (NoReftBV b v) where
  top _ = NoReft
instance F.Binder b => Top (F.ReftBV b v) where
  top _ = F.trueReft
instance F.Binder b => Top (UReftBV b v) where
  top _ = MkUReft F.trueReft pdTrue

-- | A refinement type that accepts all elements of its base type.
--
-- This is a generalization of 'F.trueReft' for the other types that instantiate
-- 'IsReft'.
trueReft :: forall r. IsReft r => r
trueReft = case toConcreteReft @r (error "trueReft") of
  ConcreteNoReft -> top (error "trueReft: ConcreteNoReft")
  ConcreteReft _ -> top (error "trueReft: ConcreteReft")
  ConcreteUReft _ -> top (error "trueReft: ConcreteUReft")

isTauto :: (IsReft r, Eq (ReftVar r)) => r -> Bool
isTauto r0 = case toConcreteReft r0 of
  ConcreteNoReft -> True
  ConcreteReft r -> F.isTautoReft r
  ConcreteUReft (MkUReft r (Pr ps)) -> F.isTautoReft r && null ps

mapReftField :: IsReft r => (F.ReftBV (ReftBind r) (ReftVar r) -> F.ReftBV (ReftBind r) (ReftVar r)) -> r -> r
mapReftField f r0 = case toConcreteReft r0 of
  ConcreteNoReft -> ofConcreteReft ConcreteNoReft
  ConcreteReft r -> ofConcreteReft (ConcreteReft (f r))
  ConcreteUReft (MkUReft r p) -> ofConcreteReft (ConcreteUReft (MkUReft (f r) p))

instance F.Binder b => IsReft (UReftBV b v) where
  type ReftVar (UReftBV b v) = v
  type ReftBind (UReftBV b v) = b
  ofConcreteReft (ConcreteUReft r) = r
  toConcreteReft = ConcreteUReft

instance (F.Binder v, F.Fixpoint v, F.Refreshable v) => Meet (F.ReftBV v v) where

instance F.Binder b => IsReft (F.ReftBV b v) where
  type ReftVar (F.ReftBV b v) = v
  type ReftBind (F.ReftBV b v) = b
  toConcreteReft = ConcreteReft
  ofConcreteReft (ConcreteReft r) = r

instance F.Binder b => IsReft (NoReftBV b v) where
  type ReftVar (NoReftBV b v) = v
  type ReftBind (NoReftBV b v) = b
  toConcreteReft _ = ConcreteNoReft
  ofConcreteReft ConcreteNoReft = NoReft

instance Top t => Top (RefB b τ t) where
  top (RProp args t) = RProp args (top t)

instance Top (PredicateBV b v) where
  top _ = pdTrue

instance (F.Binder v, F.Fixpoint v, F.Refreshable v) => Semigroup (F.ReftBV v v) where
  (<>) = F.meetReft

instance Monoid F.Reft where
  mempty  = F.trueReft
  mappend = (<>)

instance Meet (NoReftBV b v)

instance (Semigroup (F.ReftBV b v), Eq b, Eq v) => Meet (UReftBV b v)

instance (F.Refreshable v, Hashable v) => F.Subable (UReftBV v v) where
  type Variable (UReftBV v v) = v
  syms (MkUReft r p)     = F.syms r `S.union` F.syms p
  substr ns s (MkUReft r z) = MkUReft (F.substr ns s r) (F.substr ns s z)

instance Meet Predicate

pApp :: Symbol -> [Expr] -> Expr
pApp p es = F.mkEApp fn (F.EVar p:es)
  where
    fn    = F.dummyLoc $ F.symbol (pappV n)
    n     = length es

pappV :: Int -> Symbol
pappV n = F.symbol $ "papp" ++ show n
