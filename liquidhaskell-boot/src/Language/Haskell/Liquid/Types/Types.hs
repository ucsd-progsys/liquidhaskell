{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TupleSections              #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | Core types

module Language.Haskell.Liquid.Types.Types (

  -- * Ghc Information
    TyConMap     (..)

  -- * F.Located Things
  , F.Located (..)
  , F.dummyLoc

  -- * Symbols
  , F.LocSymbol
  , F.LocText

  -- * Default unknown name
  , F.dummyName
  , F.isDummy

  -- * Refinement Types
  , RTAlias (..)
  , lmapEAlias

  -- * Classes describing operations on `RTypes`
  , TyConable (..)
  , SubsTy (..)

  -- * Relational predicates
  , RelExpr
  , RelExprV (..)

  -- * Pre-instantiated RType
  , REnv
  , AREnv (..)

  -- * ???
  , Oblig(..)
  , ignoreOblig

  -- * Inferred Annotations
  , AnnInfo (..)
  , Annot (..)

  -- * Hole Information
  , HoleInfo(..)

  -- * Overall Output
  , Output (..)

  -- * Refinement Hole
  , hole, isHole, hasHole

  -- * Class for values that can be pretty printed
  , F.PPrint (..)
  , F.pprint
  , F.showpp

  -- * Modules and Imports
  , ModName (..), ModType (..)
  , isSrcImport, isSpecImport, isTarget
  , getModName, getModString, qualifyModName

  -- * Refinement Type Aliases
  , RTEnv (..), BareRTEnv, SpecRTEnv, BareRTAlias, SpecRTAlias
  -- , mapRT, mapRE

  -- * Diagnostics, Warnings, Errors and Error Messages
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
  , Measure
  , MeasureV (..)
  , UnSortedExprs, UnSortedExpr
  , MeasureKind (..)
  , CMeasure (..)
  , Def
  , DefV (..)
  , Body
  , BodyV (..)
  , MSpec (..)
  , mapDefTy
  , mapMeasureTy
  , emapDefM
  , mapDefV
  , mapMeasureV
  , emapMeasureM
  , emapRelExprV

  -- * Type Classes
  , RClass (..)

  -- * KV Profiling
  , KVKind (..)   -- types of kvars
  , KVProf        -- profile table
  , emptyKVProf   -- empty profile
  , updKVProf     -- extend profile

  -- * Misc
  , mapRTAVars

  -- * CoreToLogic
  , LogicMap(..), toLogicMap, eAppWithMap, LMap(..)

  -- * Refined Instances
  , RDEnv, DEnv(..), RInstance(..), RISig(..)
  , MethodType(..), getMethodType

  -- * String Literals
  , liquidBegin, liquidEnd

  , Axiom(..), HAxiom

  , ordSrcSpan
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
import           Data.Bifunctor
import           Data.Typeable                          (Typeable)
import           Data.Generics                          (Data)
import qualified Data.Binary                            as B
import           Data.Hashable
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import           Data.Function                          (on)
import           Data.Text                              (Text)
import           Text.PrettyPrint.HughesPJ              hiding (first, (<>))
import           Language.Fixpoint.Misc

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Expr, Symbol)

import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.GHC.Logging as GHC
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Misc


-----------------------------------------------------------------------------
-- | Information about Type Constructors
-----------------------------------------------------------------------------
data TyConMap = TyConMap
  { tcmTyRTy    :: M.HashMap TyCon             RTyCon  -- ^ Map from GHC TyCon to RTyCon
  , tcmFIRTy    :: M.HashMap (TyCon, [F.Sort]) RTyCon  -- ^ Map from GHC Family-Instances to RTyCon
  , tcmFtcArity :: M.HashMap TyCon             Int     -- ^ Arity of each Family-Tycon
  }

-----------------------------------------------------------------------------
-- | Relational predicates --------------------------------------------------
-----------------------------------------------------------------------------

type RelExpr = RelExprV F.Symbol
data RelExprV v = ERBasic (F.ExprV v) | ERChecked (F.ExprV v) (RelExprV v) | ERUnChecked (F.ExprV v) (RelExprV v)
  deriving (Eq, Show, Data, Generic, Functor, Foldable, Traversable)
  deriving B.Binary via Generically (RelExprV v)

emapRelExprV :: Monad m => ([Symbol] -> v0 -> m v1) -> RelExprV v0 -> m (RelExprV v1)
emapRelExprV f = go
  where
    go (ERBasic e) = ERBasic <$> emapExprVM f e
    go (ERChecked e re) = ERChecked <$> emapExprVM f e <*> go re
    go (ERUnChecked e re) = ERUnChecked <$> emapExprVM f e <*> go re

instance F.PPrint RelExpr where
  pprintTidy k (ERBasic e)       = F.pprintTidy k e
  pprintTidy k (ERChecked e r)   = F.pprintTidy k e <+> "!=>" <+> F.pprintTidy k r
  pprintTidy k (ERUnChecked e r) = F.pprintTidy k e <+> ":=>" <+> F.pprintTidy k r


ignoreOblig :: RType t t1 t2 -> RType t t1 t2
ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t


type SpecRTEnv   = RTEnv RTyVar SpecType
type BareRTEnv   = RTEnv Symbol BareType
type BareRTAlias = RTAlias Symbol BareType
type SpecRTAlias = RTAlias RTyVar SpecType


class SubsTy tv ty a where
  subt :: (tv, ty) -> a -> a

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

eAppWithMap :: LogicMap -> Symbol -> [Expr] -> Expr -> Expr
eAppWithMap lmap f es expr
  | Just (LMap _ xs e) <- M.lookup f (lmSymDefs lmap)
  , length xs == length es
  = F.subst (F.mkSubst $ zip xs es) e
  | otherwise
  = expr

--------------------------------------------------------------------------------
-- | Refined Instances ---------------------------------------------------------
--------------------------------------------------------------------------------

data RInstance t = RI
  { riclass :: BTyCon
    -- | The name of the dictionary
    -- Provided when resolving names
  , riDictName :: Maybe (F.Located LHName)
  , ritype  :: [t]
  , risigs  :: [(F.Located LHName, RISig t)]
  } deriving (Eq, Generic, Functor, Data, Typeable, Foldable, Traversable, Show)
    deriving Hashable via Generically (RInstance t)
    deriving B.Binary via Generically (RInstance t)

data RISig t = RIAssumed t | RISig t
  deriving (Eq, Generic, Functor, Data, Typeable, Show, Foldable, Traversable)
  deriving Hashable via Generically (RISig t)
  deriving B.Binary via Generically (RISig t)

instance F.PPrint t => F.PPrint (RISig t) where
  pprintTidy k = ppRISig k (empty :: Doc)

ppRISig :: (F.PPrint k, F.PPrint t) => F.Tidy -> k -> RISig t -> Doc
ppRISig k x (RIAssumed t) = "assume" <+> F.pprintTidy k x <+> "::" <+> F.pprintTidy k t
ppRISig k x (RISig t)     =              F.pprintTidy k x <+> "::" <+> F.pprintTidy k t

instance F.PPrint t => F.PPrint (RInstance t) where
  pprintTidy k (RI n _ ts mts) = ppMethods k "instance" n ts mts

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
                                         "\nFun Name: " ++ showPpr n ++
                                         "\nReal Name: " ++ showPpr v ++
                                         "\nData Con: " ++ showPpr c ++
                                         "\nArguments:" ++ showPpr bs  ++
                                         -- "\nTypes    :" ++ (showPpr ts)  ++
                                         "\nLHS      :" ++ showPpr lhs ++
                                         "\nRHS      :" ++ showPpr rhs

--------------------------------------------------------------------------------
-- | Refinement Type Aliases
--------------------------------------------------------------------------------
data RTAlias x a = RTA
  { rtName  :: Symbol             -- ^ name of the alias
  , rtTArgs :: [x]                -- ^ type parameters
  , rtVArgs :: [Symbol]           -- ^ value parameters
  , rtBody  :: a                  -- ^ what the alias expands to
  -- , rtMod   :: !ModName           -- ^ module where alias was defined
  } deriving (Eq, Data, Typeable, Generic, Functor, Foldable, Traversable)
    deriving Hashable via Generically (RTAlias x a)
    deriving B.Binary via Generically (RTAlias x a)
-- TODO support ghosts in aliases?

mapRTAVars :: (a -> b) -> RTAlias a ty -> RTAlias b ty
mapRTAVars f rt = rt { rtTArgs = f <$> rtTArgs rt }

lmapEAlias :: LMap -> F.Located (RTAlias Symbol Expr)
lmapEAlias (LMap v ys e) = F.atLoc v (RTA (F.val v) [] ys e) -- (F.loc v) (F.loc v)


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
  rnf REnv{} = ()

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
noErrors = null . dErrors

allWarnings :: Diagnostics -> [Warning]
allWarnings = dWarnings

allErrors :: Diagnostics -> [Error]
allErrors = dErrors

--------------------------------------------------------------------------------
-- | Printing Warnings ---------------------------------------------------------
--------------------------------------------------------------------------------

printWarning :: Logger -> Warning -> IO ()
printWarning logger (Warning srcSpan doc) = GHC.putWarnMsg logger srcSpan doc

--------------------------------------------------------------------------------
-- | Error Data Type -----------------------------------------------------------
--------------------------------------------------------------------------------

type ErrorResult    = F.FixResult UserError
type Error          = TError SpecType


instance NFData a => NFData (TError a)

--------------------------------------------------------------------------------
-- | Source Information Associated With Constraints ----------------------------
--------------------------------------------------------------------------------

data Cinfo    = Ci
  { ci_loc :: !SrcSpan
  , ci_err :: !(Maybe Error)
  , ci_var :: !(Maybe Var)
  }
  deriving (Eq, Generic)

instance F.Loc Cinfo where
  srcSpan = srcSpanFSrcSpan . ci_loc

instance NFData Cinfo

instance F.PPrint Cinfo where
  pprintTidy k = F.pprintTidy k . ci_loc

instance F.Fixpoint Cinfo where
  toFix = text . showPpr . ci_loc

instance Show Cinfo where
  show = show . F.toFix

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
type Body = BodyV F.Symbol
data BodyV v
  = E (F.ExprV v)          -- ^ Measure Refinement: {v | v = e }
  | P (F.ExprV v)          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol (F.ExprV v)   -- ^ Measure Refinement: {v | p}
  deriving (Show, Data, Typeable, Generic, Eq, Functor, Foldable, Traversable)
  deriving B.Binary via Generically (BodyV v)
  deriving Hashable via Generically (BodyV v)

emapBody
  :: Monad m
  => ([Symbol] -> v0 -> m v1)
  -> BodyV v0
  -> m (BodyV v1)
emapBody f b = case b of
    E e -> E <$> emapExprVM f e
    P e -> P <$> emapExprVM f e
    R s e -> R s <$> emapExprVM (f . (s:)) e

type Def ty ctor = DefV Symbol ty ctor
data DefV v ty ctor = Def
  { measure :: F.Located LHName
  , ctor    :: ctor
  , dsort   :: Maybe ty
  , binds   :: [(Symbol, Maybe ty)]    -- measure binders: the ADT argument fields
  , body    :: BodyV v
  } deriving (Show, Data, Typeable, Generic, Eq, Functor)
  deriving B.Binary via Generically (DefV v ty ctor)
  deriving Hashable via Generically (DefV v ty ctor)

emapDefM
  :: Monad m
  => ([Symbol] -> v0 -> m v1)
  -> ([Symbol] -> ty0 -> m ty1)
  -> DefV v0 ty0 ctor -> m (DefV v1 ty1 ctor)
emapDefM vf f d = do
    dsort <- traverse (f []) (dsort d)
    binds <- snd <$> mapAccumM (\e (s, t) -> (s:e,) . (s,) <$> traverse (f e) t) [] (binds d)
    body <- emapBody (vf . (++ map fst binds)) $ body d
    return d {dsort, binds, body}

mapDefTy :: (ty0 -> ty1) -> DefV v ty0 ctor -> DefV v ty1 ctor
mapDefTy f Def{..} =
    Def
      { dsort = fmap f dsort
      , binds = map (fmap (fmap f)) binds
      , ..
      }

mapDefV :: (v -> v') -> DefV v ty ctor -> DefV v' ty ctor
mapDefV f Def{..} =
    Def
      { body = fmap f body
      , ..
      }

type Measure ty ctor = MeasureV Symbol ty ctor
data MeasureV v ty ctor = M
  { msName :: F.Located LHName
  , msSort :: ty
  , msEqns :: [DefV v ty ctor]
  , msKind :: !MeasureKind
  , msUnSorted :: !UnSortedExprs -- potential unsorted expressions used at measure denifinitions
  } deriving (Eq, Data, Typeable, Generic, Functor)
  deriving B.Binary via Generically (MeasureV v ty ctor)
  deriving Hashable via Generically (MeasureV v ty ctor)

emapMeasureM
  :: Monad m
  => ([Symbol] -> v0 -> m v1)
  -> ([Symbol] -> ty0 -> m ty1)
  -> MeasureV v0 ty0 ctor
  -> m (MeasureV v1 ty1 ctor)
emapMeasureM vf f m = do
    msSort <- f [] (msSort m)
    msEqns <- mapM (emapDefM vf f) (msEqns m)
    return m{msSort, msEqns}

mapMeasureTy :: (ty0 -> ty1) -> MeasureV v ty0 ctor -> MeasureV v ty1 ctor
mapMeasureTy f M{..} =
    M
      { msSort = f msSort
      , msEqns = map (mapDefTy f) msEqns
      , ..
      }

mapMeasureV :: (v -> v') -> MeasureV v ty ctor -> MeasureV v' ty ctor
mapMeasureV f M{..} =
    M
      { msEqns = map (mapDefV f) msEqns
      , ..
      }

type UnSortedExprs = [UnSortedExpr] -- mempty = []
type UnSortedExpr  = ([F.Symbol], F.Expr)

data MeasureKind
  = MsReflect     -- ^ due to `reflect foo`, used for opaque reflection
  | MsMeasure     -- ^ due to `measure foo` with old-style (non-haskell) equations
  | MsLifted      -- ^ due to `measure foo` with new-style haskell equations
  | MsClass       -- ^ due to `class measure` definition
  | MsAbsMeasure  -- ^ due to `measure foo` without equations c.f. tests/pos/T1223.hs
  | MsSelector    -- ^ due to selector-fields e.g. `data Foo = Foo { fld :: Int }`
  | MsChecker     -- ^ due to checkers  e.g. `is-F` for `data Foo = F ... | G ...`
  deriving (Eq, Ord, Show, Data, Typeable, Generic)
  deriving B.Binary via Generically MeasureKind
  deriving Hashable via Generically MeasureKind

instance F.Loc (Measure a b) where
  srcSpan = F.srcSpan . msName

instance Bifunctor (DefV v) where
  -- first f  (Def m ps c s bs b) = Def m (second f <$> ps) c (f <$> s) ((second (fmap f)) <$> bs) b
  -- second f (Def m ps c s bs b) = Def m ps (f c) s bs b
  first f  (Def m c s bs b) = Def m c (f <$> s) (second (fmap f) <$> bs) b
  second f (Def m c s bs b) = Def m (f c) s bs b


instance Bifunctor (MeasureV v) where
  first  f (M n s es k u) = M n (f s) (first f <$> es) k u
  second f (M n s es k u) = M n s (second f <$> es)    k u

-- NOTE: don't use the TH versions since they seem to cause issues
-- building on windows :(
-- deriveBifunctor ''Def
-- deriveBifunctor ''Measure

data CMeasure ty = CM
  { cName :: F.Located LHName
  , cSort :: ty
  } deriving (Data, Typeable, Generic, Functor)

instance (F.PPrint v, Ord v, F.Fixpoint v) => F.PPrint (BodyV v) where
  pprintTidy k (E e)   = F.pprintTidy k e
  pprintTidy k (P p)   = F.pprintTidy k p
  pprintTidy k (R v p) = braces (F.pprintTidy k v <+> "|" <+> F.pprintTidy k p)

instance (F.PPrint a, F.PPrint v, Ord v, F.Fixpoint v) => F.PPrint (DefV v t a) where
  pprintTidy k (Def m c _ bs body)
           = F.pprintTidy k m <+> cbsd <+> "=" <+> F.pprintTidy k body
    where
      cbsd = parens (F.pprintTidy k c <-> hsep (F.pprintTidy k `fmap` (fst <$> bs)))

instance (F.PPrint v, Ord v, F.Fixpoint v, F.PPrint t, F.PPrint a) => F.PPrint (MeasureV v t a) where
  pprintTidy k (M n s eqs _ _) =  F.pprintTidy k n <+> {- parens (pprintTidy k (loc n)) <+> -} "::" <+> F.pprintTidy k s
                                  $$ vcat (F.pprintTidy k `fmap` eqs)


instance F.PPrint (MeasureV v t a) => Show (MeasureV v t a) where
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
  , rcMethods :: [(F.Located LHName, ty)]
  } deriving (Eq, Show, Functor, Data, Typeable, Generic, Foldable, Traversable)
    deriving B.Binary via Generically (RClass ty)
    deriving Hashable via Generically (RClass ty)


instance F.PPrint t => F.PPrint (RClass t) where
  pprintTidy k (RClass n ts as mts)
                = ppMethods k ("class" <+> supers ts) n as [(m, RISig t) | (m, t) <- mts]
    where
      supers [] = ""
      supers xs = tuplify (F.pprintTidy k   <$> xs) <+> "=>"
      tuplify   = parens . hcat . punctuate ", "


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

hole :: F.ExprV v
hole = F.PKVar "HOLE" (F.Su mempty)

isHole :: Expr -> Bool
isHole (F.PKVar "HOLE" _) = True
isHole _                  = False

hasHole :: Reftable r => r -> Bool
hasHole = any isHole . F.conjuncts . F.reftPred . toReft

instance F.Symbolic DataCon where
  symbol = F.symbol . dataConWorkId

instance Ord TyCon where
  compare = compare `on` F.symbol

instance Ord DataCon where
  compare = compare `on` F.symbol

instance F.PPrint TyThing where
  pprintTidy _ = text . showPpr

-- instance F.Symbolic TyThing where
--  symbol = tyThingSymbol

liquidBegin :: String
liquidBegin = ['{', '-', '@']

liquidEnd :: String
liquidEnd = ['@', '-', '}']

data MSpec ty ctor = MSpec
  { ctorMap  :: M.HashMap LHName [Def ty ctor]
  , measMap  :: M.HashMap (F.Located LHName) (Measure ty ctor)
  , cmeasMap :: M.HashMap (F.Located LHName) (Measure ty ())
  , imeas    :: ![Measure ty ctor]
  } deriving (Data, Typeable, Generic, Functor)

instance Bifunctor MSpec   where
  first f (MSpec c m cm im) = MSpec (fmap (fmap (first f)) c)
                                    (fmap (first f) m)
                                    (fmap (first f) cm)
                                    (fmap (first f) im)
  second                    = fmap

instance (F.PPrint t, F.PPrint a) => F.PPrint (MSpec t a) where
  pprintTidy k =  vcat . fmap (F.pprintTidy k . snd) . M.toList . measMap

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
      dups = [(k1, k2) | k1 <- M.keys m1 , k2 <- M.keys m2, F.val k1 == F.val k2, F.loc k1 /= F.loc k2]
      err k1 k2 = ErrDupMeas (fSrcSpan k1) (F.pprint (F.val k1)) (fSrcSpan <$> [k1, k2])


instance Eq ctor => Monoid (MSpec ty ctor) where
  mempty = MSpec M.empty M.empty M.empty []
  mappend = (<>)
