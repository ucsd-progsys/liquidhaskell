{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE OverlappingInstances   #-}

-- | This module (should) contain all the global type definitions and basic
-- instances. Need to gradually pull things into here, especially from @RefType@

module Language.Haskell.Liquid.Types (

  -- * Options
    Config (..)

  -- * Ghc Information
  , GhcInfo (..)
  , GhcSpec (..)
  , TargetVars (..)

  -- * Located Things
  , Located (..)

  -- * Symbols
  , LocSymbol
  , LocString

  -- * Data Constructors
  , BDataCon (..)

  -- * Constructors and Destructors
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow 
  , mkUnivs, bkUniv, bkClass
  , rFun

  -- * Manipulating Predicate
  , pvars

  -- * All these should be MOVE TO TYPES
  , RTyVar (..), RType (..), RRType, BRType, RTyCon(..)
  , TyConable (..), RefTypable (..), SubsTy (..), Ref(..)
  , RTAlias (..), mapRTAVars
  , BSort, BPVar, BareType, RSort, UsedPVar, RPVar, RReft, RefType
  , PrType, SpecType
  , PVar (..) , Predicate (..), UReft(..), DataDecl (..), TyConInfo(..)
  , TyConP (..), DataConP (..)

  -- * Default unknown name
  , dummyName, isDummy
  
  -- * Traversing `RType` 
  , efoldReft, foldReft
  , mapReft, mapReftM
  , mapBot, mapBind
  
  , isTrivial
  
  -- * Converting To and From Sort
  , ofRSort, toRSort
  , rTypeValueVar
  , rTypeReft
  , stripRTypeBase 

  -- * Class for values that can be pretty printed 
  , PPrint (..)
  , showpp
  
  -- * Printer Configuration 
  , PPEnv (..), ppEnv

  -- * Import handling
  , ModName (..), ModType (..), isSrcImport, isSpecImport
  , getModName, getModString

  -- * Refinement Type Aliases
  , RTEnv (..), mapRT, mapRP, RTBareOrSpec

  -- * Final Result
  , Result (..)

  -- * Different kinds of errors
  , Error (..)
  , ErrorResult

  -- * Source information associated with each constraint
  , Cinfo (..)

  -- * Measures
  , Measure (..)
  -- , IMeasure (..)
  , CMeasure (..)
  , Def (..)
  , Body (..)
  -- * Type Classes
  , RClass (..)
  )
  where

import FastString                               (fsLit)
import SrcLoc                                   (mkGeneralSrcSpan, SrcSpan)
import TyCon
import DataCon
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Var
import Unique
import Literal
import Text.Printf
import GHC                          (Class, HscEnv, ModuleName, Name, moduleNameString)
import GHC                          (Class, HscEnv)
import Language.Haskell.Liquid.GhcMisc 

import Control.Arrow (second)
import Control.Monad  (liftM, liftM2, liftM3)
import Control.DeepSeq
import Control.Applicative          ((<$>))
import Data.Typeable                (Typeable)
import Data.Generics                (Data)   
import Data.Monoid                  hiding ((<>))
import qualified Data.Foldable as F
import Data.Hashable
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Function                (on)
import Data.Maybe                   (maybeToList, fromMaybe)
import Data.Traversable             hiding (mapM)
import Data.List                    (nub, union, unionBy)
import Text.Parsec.Pos              (SourcePos, newPos) 
import Text.Parsec.Error            (ParseError) 
import Text.PrettyPrint.HughesPJ    
import Language.Fixpoint.Config     hiding (Config) 
import Language.Fixpoint.Misc
import Language.Fixpoint.Types      hiding (Predicate, Def) 
-- import qualified Language.Fixpoint.Types as F

import CoreSyn (CoreBind)
import Var
-----------------------------------------------------------------------------
-- | Command Line Config Options --------------------------------------------
-----------------------------------------------------------------------------

-- NOTE: adding strictness annotations breaks the help message
data Config = Config { 
    files          :: [FilePath] -- ^ source files to check
  , idirs          :: [FilePath] -- ^ path to directory for including specs
  , diffcheck      :: Bool       -- ^ check subset of binders modified (+ dependencies) since last check 
  , binders        :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , totality       :: Bool       -- ^ check totality in definitions
  , noPrune        :: Bool       -- ^ disable prunning unsorted Refinements
  , maxParams      :: Int        -- ^ the maximum number of parameters to accept when mining qualifiers
  , smtsolver      :: SMTSolver  -- ^ name of smtsolver to use [default: z3-API]  
  } deriving (Data, Typeable, Show, Eq)

-----------------------------------------------------------------------------
-- | Printer ----------------------------------------------------------------
-----------------------------------------------------------------------------

class PPrint a where
  pprint :: a -> Doc

showpp :: (PPrint a) => a -> String 
showpp = render . pprint 

-- pshow :: PPrint a => a -> String
-- pshow = render . pprint

instance PPrint a => PPrint (Maybe a) where
  pprint = maybe (text "Nothing") ((text "Just" <+>) . pprint)

instance PPrint a => PPrint [a] where
  pprint = brackets . intersperse comma . map pprint



instance (PPrint a, PPrint b) => PPrint (a,b) where
  pprint (x, y)  = (pprint x) <+> text ":" <+> (pprint y)

data PPEnv 
  = PP { ppPs    :: Bool
       , ppTyVar :: Bool
       }

ppEnv           = ppEnvPrintPreds
ppEnvCurrent    = PP False False
ppEnvPrintPreds = PP True False


-----------------------------------------------------------------------------
-- | Located Values ---------------------------------------------------------
-----------------------------------------------------------------------------

data Located a = Loc { loc :: !SourcePos
                     , val :: a
                     }

type LocSymbol = Located Symbol
type LocString = Located String

dummyName = "dummy"

isDummy :: (Show a) => a -> Bool
isDummy a = show a == dummyName


instance Fixpoint SourcePos where
  toFix = text . show 

instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val 

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val 

instance Expression a => Expression (Located a) where
  expr   = expr . val

instance Functor Located where
  fmap f (Loc l x) =  Loc l (f x)

instance F.Foldable Located where
  foldMap f (Loc _ x) = f x

instance Traversable Located where 
  traverse f (Loc l x) = Loc l <$> f x

instance Show a => Show (Located a) where
  show (Loc l x) = show x ++ " defined at " ++ show l

instance Eq a => Eq (Located a) where
  (Loc _ x) == (Loc _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance Subable a => Subable (Located a) where
  syms (Loc _ x)     = syms x
  substa f (Loc l x) = Loc l (substa f x)
  substf f (Loc l x) = Loc l (substf f x)
  subst su (Loc l x) = Loc l (subst su x)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val



------------------------------------------------------------------
-- | GHC Information :  Code & Spec ------------------------------
------------------------------------------------------------------
 
data GhcInfo = GI { 
    env      :: !HscEnv
  , cbs      :: ![CoreBind]
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
    tySigs     :: ![(Var, Located SpecType)]     -- ^ Asserted/Assumed Reftypes
                                                 -- eg.  see include/Prelude.spec
  , ctors      :: ![(Var, Located SpecType)]     -- ^ Data Constructor Measure Sigs
                                                 -- eg.  (:) :: a -> xs:[a] -> {v: Int | v = 1 + len(xs) }
  , meas       :: ![(Symbol, Located RefType)]   -- ^ Measure Types  
                                                 -- eg.  len :: [a] -> Int
  , invariants :: ![Located SpecType]            -- ^ Data Type Invariants
                                                 -- eg.  forall a. {v: [a] | len(v) >= 0}
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
  , lvars      :: !(S.HashSet Var)               -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet Var)               -- ^ Binders to IGNORE during termination checking
  , config     :: !Config                        -- ^ Configuration Options
  }


data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar RSort)]
                     , covPs        :: ![Int] -- indexes of covariant predicate arguments
                     , contravPs    :: ![Int] -- indexes of contravariant predicate arguments
                     , sizeFun      :: !(Maybe (Symbol -> Expr))
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar RSort)]
                         , tyConsts   :: ![SpecType]
                         , tyArgs     :: ![(Symbol, SpecType)]
                         , tyRes      :: !SpecType
                         }


-- | Which Top-Level Binders Should be Verified
data TargetVars = AllVars | Only ![Var]


--------------------------------------------------------------------
-- | Predicate Variables -------------------------------------------
--------------------------------------------------------------------

-- MOVE TO TYPES
data PVar t
  = PV { pname :: !Symbol
       , ptype :: !t
       , pargs :: ![(t, Symbol, Expr)]
       }
	deriving (Show)

instance Eq (PVar t) where
  pv == pv' = (pname pv == pname pv') {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _)  (PV n' _ _) = compare n n'

instance Functor PVar where
  fmap f (PV x t txys) = PV x (f t) (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t txys) = rnf n `seq` rnf t `seq` rnf txys

instance Hashable (PVar a) where
  hashWithSalt i (PV n _ xys) = hashWithSalt i  n -- : (thd3 <$> xys)

--------------------------------------------------------------------
------------------ Predicates --------------------------------------
--------------------------------------------------------------------

type UsedPVar      = PVar ()
newtype Predicate  = Pr [UsedPVar] -- deriving (Data, Typeable) 

instance NFData Predicate where
  rnf _ = ()

instance Monoid Predicate where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Monoid a) => Monoid (UReft a) where
  mempty                    = U mempty mempty
  mappend (U x y) (U x' y') = U (mappend x x') (mappend y y')


pdTrue         = Pr []
pdAnd ps       = Pr (nub $ concatMap pvars ps)
pvars (Pr pvs) = pvs

-- MOVE TO TYPES
instance Subable UsedPVar where 
  syms pv         = [ y | (_, x, EVar y) <- pargs pv, x /= y ]
  subst s pv      = pv { pargs = mapThd3 (subst s)  <$> pargs pv }  
  substf f pv     = pv { pargs = mapThd3 (substf f) <$> pargs pv }  
  substa f pv     = pv { pargs = mapThd3 (substa f) <$> pargs pv }  


-- MOVE TO TYPES
instance Subable Predicate where
  syms (Pr pvs)     = concatMap syms pvs 
  subst s (Pr pvs)  = Pr (subst s <$> pvs)
  substf f (Pr pvs) = Pr (substf f <$> pvs)
  substa f (Pr pvs) = Pr (substa f <$> pvs)



instance NFData r => NFData (UReft r) where
  rnf (U r p) = rnf r `seq` rnf p

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()


-- MOVE TO TYPES
newtype RTyVar = RTV TyVar

data RTyCon = RTyCon 
  { rTyCon     :: !TyCon            -- GHC Type Constructor
  , rTyConPs   :: ![RPVar]          -- Predicate Parameters
  , rTyConInfo :: !TyConInfo        -- TyConInfo
  }
  -- deriving (Data, Typeable)

-----------------------------------------------------------------------
----------- TyCon get CoVariance - ContraVariance Info ----------------
-----------------------------------------------------------------------

-- indexes start from 0 and type or predicate arguments can be both
-- covariant and contravaariant
-- eg, for the below Foo dataType
-- data Foo a b c d <p :: b -> Prop, q :: Int -> Prop, r :: a -> Prop>
--   = F (a<r> -> b<p>) | Q (c -> a) | G (Int<q> -> a<r>)
-- there will be 
--  covariantTyArgs     = [0, 1, 3], for type arguments a, b and d
--  contravariantTyArgs = [0, 2, 3], for type arguments a, c and d
--  covariantPsArgs     = [0, 2], for predicate arguments p and r
--  contravariantPsArgs = [1, 2], for predicate arguments q and r
--  
--  Note, d does not appear in the data definition, we enforce BOTH
--  con - contra variance

data TyConInfo = TyConInfo
  { covariantTyArgs     :: ![Int] -- indexes of covariant type arguments
  , contravariantTyArgs :: ![Int] -- indexes of contravariant type arguments
  , covariantPsArgs     :: ![Int] -- indexes of covariant predicate arguments
  , contravariantPsArgs :: ![Int] -- indexes of contravariant predicate arguments
  , sizeFunction        :: !(Maybe (Symbol -> Expr))
  }


--------------------------------------------------------------------
---- Unified Representation of Refinement Types --------------------
--------------------------------------------------------------------

-- MOVE TO TYPES
data RType p c tv r
  = RVar { 
      rt_var    :: !tv
    , rt_reft   :: !r 
    }
  
  | RFun  {
      rt_bind   :: !Symbol
    , rt_in     :: !(RType p c tv r)
    , rt_out    :: !(RType p c tv r) 
    , rt_reft   :: !r
    }

  | RAllT { 
      rt_tvbind :: !tv       
    , rt_ty     :: !(RType p c tv r)
    }

  | RAllP {
      rt_pvbind :: !(PVar (RType p c tv ()))
    , rt_ty     :: !(RType p c tv r)
    }

  | RApp  { 
      rt_tycon  :: !c
    , rt_args   :: ![(RType p c tv r)]     
    , rt_pargs  :: ![Ref (RType p c tv ()) r (RType p c tv r)] 
    , rt_reft   :: !r
    }

  | RCls  { 
      rt_class  :: !p
    , rt_args   :: ![(RType p c tv r)]
    }

  | RAllE { 
      rt_bind   :: !Symbol
    , rt_allarg :: !(RType p c tv r)
    , rt_ty     :: !(RType p c tv r) 
    }

  | REx { 
      rt_bind   :: !Symbol
    , rt_exarg  :: !(RType p c tv r) 
    , rt_ty     :: !(RType p c tv r) 
    }

  | RExprArg Expr                               -- ^ For expression arguments to type aliases
                                                --   see tests/pos/vector2.hs
  | RAppTy{
      rt_arg   :: !(RType p c tv r)
    , rt_res   :: !(RType p c tv r)
    , rt_reft  :: !r
    }

  | ROth  !String 

-- MOVE TO TYPES

data Ref t s m 
  = RMono [(Symbol, t)] s 
  | RPoly [(Symbol, t)] m

-- MOVE TO TYPES
data UReft r
  = U { ur_reft :: !r, ur_pred :: !Predicate }

-- MOVE TO TYPES
type BRType     = RType String String String   
type RRType     = RType Class  RTyCon RTyVar   

type BSort      = BRType    ()
type RSort      = RRType    ()

type BPVar      = PVar      BSort
type RPVar      = PVar      RSort

type RReft      = UReft     Reft 
type PrType     = RRType    Predicate
type BareType   = BRType    RReft
type SpecType   = RRType    RReft 
type RefType    = RRType    Reft


class SubsTy tv ty a where
  subt :: (tv, ty) -> a -> a


-- MOVE TO TYPES
class (Eq c) => TyConable c where
  isFun    :: c -> Bool
  isList   :: c -> Bool
  isTuple  :: c -> Bool
  ppTycon  :: c -> Doc

-- MOVE TO TYPES
class ( TyConable c
      , Eq p, Eq c, Eq tv
      , Hashable tv
      , Reftable r
      , PPrint r
      ) => RefTypable p c tv r 
  where
    ppCls    :: p -> [RType p c tv r] -> Doc
    ppRType  :: Prec -> RType p c tv r -> Doc 
    -- ppRType  = ppr_rtype True -- False 
    -- ppBase   :: r -> Doc -> Doc

--------------------------------------------------------------------------
-- | Values Related to Specifications ------------------------------------
--------------------------------------------------------------------------

-- | Data type refinements
data DataDecl   = D { tycName   :: String                           -- ^ Type  Constructor Name 
                    , tycTyVars :: [String]                         -- ^ Tyvar Parameters
                    , tycPVars  :: [PVar BSort]                     -- ^ PVar  Parameters
                    , tycDCons  :: [(String, [(String, BareType)])] -- ^ [DataCon, [(fieldName, fieldType)]]   
                    , tycSrcPos :: !SourcePos                       -- ^ Source Position
                    , tycSFun   :: (Maybe (Symbol -> Expr))         -- ^ Measure that should decrease in recursive calls
                    }
     --              deriving (Show) 

-- | Refinement Type Aliases

data RTAlias tv ty 
  = RTA { rtName  :: String
        , rtTArgs :: [tv]
        , rtVArgs :: [tv] 
        , rtBody  :: ty  
        , srcPos  :: SourcePos 
        }

mapRTAVars f rt = rt { rtTArgs = f <$> rtTArgs rt
                     , rtVArgs = f <$> rtVArgs rt
                     }

-- | Datacons

data BDataCon a 
  = BDc a       -- ^ Raw named data constructor
  | BTup Int    -- ^ Tuple constructor + arity
  deriving (Eq, Ord, Show)

instance Functor BDataCon where
  fmap f (BDc x)  = BDc (f x)
  fmap f (BTup i) = BTup i

instance Hashable a => Hashable (BDataCon a) where
  hashWithSalt i (BDc x)  = hashWithSalt i x
  hashWithSalt i (BTup j) = hashWithSalt i j

------------------------------------------------------------------------
-- | Constructor and Destructors for RTypes ----------------------------
------------------------------------------------------------------------

mkArrow αs πs xts = mkUnivs αs πs . mkArrs xts 
  where 
    mkArrs xts t  = foldr (uncurry rFun) t xts 

bkArrowDeep (RAllT _ t)     = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RFun x t t' _) = let (xs, ts, t'') = bkArrowDeep t'  in (x:xs, t:ts, t'')
bkArrowDeep t               = ([], [], t)

bkArrow (RFun x t t' _) = let (xs, ts, t'') = bkArrow t'  in (x:xs, t:ts, t'')
bkArrow t               = ([], [], t)

safeBkArrow (RAllT _ _) = errorstar "safeBkArrow on RAllT"
safeBkArrow (RAllP _ _) = errorstar "safeBkArrow on RAllT"
safeBkArrow t           = bkArrow t

mkUnivs αs πs t = foldr RAllT (foldr RAllP t πs) αs 

bkUniv :: RType t t1 a t2 -> ([a], [PVar (RType t t1 a ())], RType t t1 a t2)
bkUniv (RAllT α t)      = let (αs, πs, t') = bkUniv t in  (α:αs, πs, t') 
bkUniv (RAllP π t)      = let (αs, πs, t') = bkUniv t in  (αs, π:πs, t') 
bkUniv t                = ([], [], t)

bkClass (RFun _ (RCls c t) t' _) = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass t                        = ([], t)

rFun b t t' = RFun b t t' top


--------------------------------------------

instance (PPrint r, Reftable r) => Reftable (UReft r) where
  isTauto            = isTauto_ureft 
  -- ppTy (U r p) d     = ppTy r (ppTy p d) 
  ppTy               = ppTy_ureft
  toReft (U r _)     = toReft r
  params (U r _)     = params r
  bot (U r _)        = U (bot r) (Pr [])

isTauto_ureft u      = isTauto (ur_reft u) && isTauto (ur_pred u)

ppTy_ureft u@(U r p) d 
  | isTauto_ureft u  = d
  | otherwise        = ppr_reft r (ppTy p d)

ppr_reft r d         = braces (toFix v <+> colon <+> d <+> text "|" <+> pprint r')
  where 
    r'@(Reft (v, _)) = toReft r


instance Subable r => Subable (UReft r) where
  syms (U r p)     = syms r ++ syms p 
  subst s (U r z)  = U (subst s r) (subst s z)
  substf f (U r z) = U (substf f r) (substf f z) 
  substa f (U r z) = U (substa f r) (substa f z) 
 
instance (Reftable r, RefTypable p c tv r) => Subable (Ref (RType p c tv ()) r (RType p c tv r)) where
  syms (RMono ss r)     = (fst <$> ss) ++ syms r
  syms (RPoly ss r)     = (fst <$> ss) ++ syms r

  subst su (RMono ss r) = RMono ss (subst su r)
  subst su (RPoly ss t) = RPoly ss (subst su <$> t)

  substf f (RMono ss r) = RMono ss (substf f r) 
  substf f (RPoly ss t) = RPoly ss (substf f <$> t)
  substa f (RMono ss r) = RMono ss (substa f r) 
  substa f (RPoly ss t) = RPoly ss (substa f <$> t)

instance (Subable r, RefTypable p c tv r) => Subable (RType p c tv r) where
  syms        = foldReft (\r acc -> syms r ++ acc) [] 
  substa f    = mapReft (substa f) 
  substf f    = emapReft (substf . substfExcept f) [] 
  subst su    = emapReft (subst  . substExcept su) []
  subst1 t su = emapReft (\xs r -> subst1Except xs r su) [] t




instance Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = errorstar "No BOT instance for Predicate"
  -- HACK: Hiding to not render types in WEB DEMO. NEED TO FIX.
  ppTy r d | isTauto r        = d 
           | not (ppPs ppEnv) = d
           | otherwise        = d <> (angleBrackets $ pprint r)
  
  toReft               = errorstar "TODO: instance of toReft for Predicate"
  params               = errorstar "TODO: instance of params for Predicate"


---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

isTrivial t = foldReft (\r b -> isTauto r && b) True t

instance Functor UReft where
  fmap f (U r p) = U (f r) p

instance Functor (RType a b c) where
  fmap  = mapReft 

-- instance Fold.Foldable (RType a b c) where
--   foldr = foldReft

mapReft ::  (r1 -> r2) -> RType p c tv r1 -> RType p c tv r2
mapReft f = emapReft (\_ -> f) []

emapReft ::  ([Symbol] -> r1 -> r2) -> [Symbol] -> RType p c tv r1 -> RType p c tv r2

emapReft f γ (RVar α r)          = RVar  α (f γ r)
emapReft f γ (RAllT α t)         = RAllT α (emapReft f γ t)
emapReft f γ (RAllP π t)         = RAllP π (emapReft f γ t)
emapReft f γ (RFun x t t' r)     = RFun  x (emapReft f γ t) (emapReft f (x:γ) t') (f γ r)
emapReft f γ (RApp c ts rs r)    = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (RCls c ts)         = RCls  c (emapReft f γ <$> ts) 
emapReft f γ (RAllE z t t')      = RAllE z (emapReft f γ t) (emapReft f γ t')
emapReft f γ (REx z t t')        = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)        = RExprArg e
emapReft f γ (RAppTy t t' r)     = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft _ _ (ROth s)            = ROth  s 

emapRef :: ([Symbol] -> t -> s) ->  [Symbol] -> Ref (RType p c tv ()) t (RType p c tv t) -> Ref (RType p c tv ()) s (RType p c tv s)
emapRef  f γ (RMono s r)         = RMono s $ f γ r
emapRef  f γ (RPoly s t)         = RPoly s $ emapReft f γ t

------------------------------------------------------------------------------------------------------


mapReftM :: (Monad m) => (r1 -> m r2) -> RType p c tv r1 -> m (RType p c tv r2)
mapReftM f (RVar α r)         = liftM   (RVar  α)   (f r)
mapReftM f (RAllT α t)        = liftM   (RAllT α)   (mapReftM f t)
mapReftM f (RAllP π t)        = liftM   (RAllP π)   (mapReftM f t)
mapReftM f (RFun x t t' r)    = liftM3  (RFun x)    (mapReftM f t)          (mapReftM f t')       (f r)
mapReftM f (RApp c ts rs r)   = liftM3  (RApp  c)   (mapM (mapReftM f) ts)  (mapM (mapRefM f) rs) (f r)
mapReftM f (RCls c ts)        = liftM   (RCls  c)   (mapM (mapReftM f) ts) 
mapReftM f (RAllE z t t')     = liftM2  (RAllE z)   (mapReftM f t)          (mapReftM f t')
mapReftM f (REx z t t')       = liftM2  (REx z)     (mapReftM f t)          (mapReftM f t')
mapReftM _ (RExprArg e)       = return  $ RExprArg e 
mapReftM f (RAppTy t t' r)    = liftM3 (RAppTy) (mapReftM f t) (mapReftM f t') (f r)
mapReftM _ (ROth s)           = return  $ ROth  s 

mapRefM  :: (Monad m) => (t -> m s) -> Ref (RType p c tv ()) t (RType p c tv t) -> m (Ref (RType p c tv ()) s (RType p c tv s))
mapRefM  f (RMono s r)        = liftM   (RMono s)      (f r)
mapRefM  f (RPoly s t)        = liftM   (RPoly s)      (mapReftM f t)

-- foldReft :: (r -> a -> a) -> a -> RType p c tv r -> a
foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) emptySEnv 

-- efoldReft :: Reftable r =>(p -> [RType p c tv r] -> [(Symbol, a)])-> (RType p c tv r -> a)-> (SEnv a -> Maybe (RType p c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType p c tv r-> c1
efoldReft cb g f = go 
  where
    -- folding over RType 
    go γ z me@(RVar _ r)                = f γ (Just me) r z 
    go γ z (RAllT _ t)                  = go γ z t
    go γ z (RAllP _ t)                  = go γ z t
    go γ z me@(RFun _ (RCls c ts) t' r) = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t') 
    go γ z me@(RFun x t t' r)           = f γ (Just me) r (go (insertSEnv x (g t) γ) (go γ z t) t')
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' (insertSEnv (rTypeValueVar me) (g me) γ) z ts) rs)
    
    go γ z (RCls c ts)                  = go' γ z ts
    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t' 
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t' 
    go _ z (ROth _)                     = z 
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z

    -- folding over Ref 
    ho  γ z (RMono ss r)                = f (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) Nothing r z
    ho  γ z (RPoly ss t)                = go (insertsSEnv γ ((mapSnd (g . ofRSort)) <$> ss)) z t
   
    -- folding over [RType]
    go' γ z ts                 = foldr (flip $ go γ) z ts 

    -- folding over [Ref]
    ho' γ z rs                 = foldr (flip $ ho γ) z rs 

-- ORIG delete after regrtest-ing specerror
-- -- efoldReft :: (RType p c tv r -> b) -> (SEnv b -> Maybe (RType p c tv r) -> r -> a -> a) -> SEnv b -> a -> RType p c tv r -> a
-- efoldReft g f γ z me@(RVar _ r)       = f γ (Just me) r z 
-- efoldReft g f γ z (RAllT _ t)         = efoldReft g f γ z t
-- efoldReft g f γ z (RAllP _ t)         = efoldReft g f γ z t
-- efoldReft g f γ z me@(RFun x t t' r)  = f γ (Just me) r (efoldReft g f (insertSEnv x (g t) γ) (efoldReft g f γ z t) t')
-- efoldReft g f γ z me@(RApp _ ts rs r) = f γ (Just me) r (efoldRefs g f γ (efoldRefts g f (insertSEnv (rTypeValueVar me) (g me) γ) z ts) rs)
-- efoldReft g f γ z (RCls _ ts)         = efoldRefts g f γ z ts
-- efoldReft g f γ z (RAllE x t t')      = efoldReft g f (insertSEnv x (g t) γ) (efoldReft g f γ z t) t' 
-- efoldReft g f γ z (REx x t t')        = efoldReft g f (insertSEnv x (g t) γ) (efoldReft g f γ z t) t' 
-- efoldReft _ _ _ z (ROth _)            = z 
-- efoldReft g f γ z me@(RAppTy t t' r)  = f γ (Just me) r (efoldReft g f γ (efoldReft g f γ z t) t')
-- efoldReft _ _ _ z (RExprArg _)        = z
-- 
-- -- efoldRefts :: (RType p c tv r -> b) -> (SEnv b -> Maybe (RType p c tv r) -> r -> a -> a) -> SEnv b -> a -> [RType p c tv r] -> a
-- efoldRefts g f γ z ts                = foldr (flip $ efoldReft g f γ) z ts 
-- 
-- -- efoldRefs :: (RType p c tv r -> b) -> (SEnv b -> Maybe (RType p c tv r) -> r -> a -> a) -> SEnv b -> a -> [Ref r (RType p c tv r)] -> a
-- efoldRefs g f γ z rs               = foldr (flip $ efoldRef g f γ) z  rs 
-- 
-- -- efoldRef :: (RType p c tv r -> b) -> (SEnv b -> Maybe (RType p c tv r) -> r -> a -> a) -> SEnv b -> a -> Ref r (RType p c tv r) -> a
-- efoldRef g f γ z (RMono ss r)         = f (insertsSEnv γ (mapSnd (g . ofRSort) <$> ss)) Nothing r z
-- efoldRef g f γ z (RPoly ss t)         = efoldReft g f (insertsSEnv γ ((mapSnd (g . ofRSort)) <$> ss)) z t

mapBot f (RAllT α t)       = RAllT α (mapBot f t)
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RFun x t t' r)   = RFun x (mapBot f t) (mapBot f t') r
mapBot f (RAppTy t t' r)   = RAppTy (mapBot f t) (mapBot f t') r
mapBot f (RApp c ts rs r)  = f $ RApp c (mapBot f <$> ts) (mapBotRef f <$> rs) r
mapBot f (RCls c ts)       = RCls c (mapBot f <$> ts)
mapBot f (REx b t1 t2)     = REx b  (mapBot f t1) (mapBot f t2)
mapBot f (RAllE b t1 t2)   = RAllE b  (mapBot f t1) (mapBot f t2)
mapBot f t'                = f t' 
mapBotRef _ (RMono s r)    = RMono s $ r
mapBotRef f (RPoly s t)    = RPoly s $ mapBot f t

mapBind f (RAllT α t)      = RAllT α (mapBind f t)
mapBind f (RAllP π t)      = RAllP π (mapBind f t)
mapBind f (RFun b t1 t2 r) = RFun (f b)  (mapBind f t1) (mapBind f t2) r
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RCls c ts)      = RCls c (mapBind f <$> ts)
mapBind f (RAllE b t1 t2)  = RAllE  (f b) (mapBind f t1) (mapBind f t2)
mapBind f (REx b t1 t2)    = REx    (f b) (mapBind f t1) (mapBind f t2)
mapBind _ (RVar α r)       = RVar α r
mapBind _ (ROth s)         = ROth s
mapBind f (RAppTy t1 t2 r) = RAppTy (mapBind f t1) (mapBind f t2) r
mapBind _ (RExprArg e)     = RExprArg e

mapBindRef f (RMono s r)   = RMono (mapFst f <$> s) r
mapBindRef f (RPoly s t)   = RPoly (mapFst f <$> s) $ mapBind f t


--------------------------------------------------
ofRSort ::  Reftable r => RType p c tv () -> RType p c tv r 
ofRSort = fmap (\_ -> top)

toRSort :: RType p c tv r -> RType p c tv () 
toRSort = stripQuantifiers . mapBind (const dummySymbol) . fmap (const ())

stripQuantifiers (RAllT α t)      = RAllT α (stripQuantifiers t)
stripQuantifiers (RAllP _ t)      = stripQuantifiers t
stripQuantifiers (RAllE _ _ t)    = stripQuantifiers t
stripQuantifiers (REx _ _ t)      = stripQuantifiers t
stripQuantifiers (RFun x t t' r)  = RFun x (stripQuantifiers t) (stripQuantifiers t') r
stripQuantifiers (RAppTy t t' r)  = RAppTy (stripQuantifiers t) (stripQuantifiers t') r
stripQuantifiers (RApp c ts rs r) = RApp c (stripQuantifiers <$> ts) (stripQuantifiersRef <$> rs) r
stripQuantifiers (RCls c ts)      = RCls c (stripQuantifiers <$> ts)
stripQuantifiers t                = t
stripQuantifiersRef (RPoly s t)   = RPoly s $ stripQuantifiers t
stripQuantifiersRef r             = r


insertsSEnv  = foldr (\(x, t) γ -> insertSEnv x t γ)

rTypeValueVar :: (Reftable r) => RType p c tv r -> Symbol
rTypeValueVar t = vv where Reft (vv,_) =  rTypeReft t 
rTypeReft :: (Reftable r) => RType p c tv r -> Reft
rTypeReft = fromMaybe top . fmap toReft . stripRTypeBase 

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

-----------------------------------------------------------------------------
-- | PPrint -----------------------------------------------------------------
-----------------------------------------------------------------------------

instance PPrint SourcePos where
  pprint = text . show 

instance PPrint () where
  pprint = text . show 

instance PPrint String where 
  pprint = text 

instance PPrint a => PPrint (Located a) where
  pprint = pprint . val 

instance PPrint Int where
  pprint = toFix

instance PPrint Integer where
  pprint = toFix

instance PPrint Constant where
  pprint = toFix

instance PPrint Brel where
  pprint Eq = text "=="
  pprint Ne = text "/="
  pprint r  = toFix r

instance PPrint Bop where
  pprint  = toFix 

instance PPrint Sort where
  pprint = toFix  

instance PPrint Symbol where
  pprint = toFix

instance PPrint Expr where
  pprint (EApp f es)     = parens $ intersperse empty $ (pprint f) : (pprint <$> es) 
  pprint (ECon c)        = pprint c 
  pprint (EVar s)        = pprint s
  pprint (ELit s _)      = pprint s
  pprint (EBin o e1 e2)  = parens $ pprint e1 <+> pprint o <+> pprint e2
  pprint (EIte p e1 e2)  = parens $ text "if" <+> pprint p <+> text "then" <+> pprint e1 <+> text "else" <+> pprint e2 
  pprint (ECst e so)     = parens $ pprint e <+> text " : " <+> pprint so 
  pprint (EBot)          = text "_|_"

instance PPrint Pred where
  pprint PTop            = text "???"
  pprint PTrue           = trueD 
  pprint PFalse          = falseD
  pprint (PBexp e)       = parens $ pprint e
  pprint (PNot p)        = parens $ text "not" <+> parens (pprint p)
  pprint (PImp p1 p2)    = parens $ (pprint p1) <+> text "=>"  <+> (pprint p2)
  pprint (PIff p1 p2)    = parens $ (pprint p1) <+> text "<=>" <+> (pprint p2)
  pprint (PAnd ps)       = parens $ pprintBin trueD  andD ps
  pprint (POr  ps)       = parens $ pprintBin falseD orD  ps 
  pprint (PAtom r e1 e2) = parens $ pprint e1 <+> pprint r <+> pprint e2
  pprint (PAll xts p)    = text "forall" <+> toFix xts <+> text "." <+> pprint p

trueD  = text "true"
falseD = text "false"
andD   = text " &&"
orD    = text " ||"

pprintBin b _ []     = b
pprintBin _ o xs     = intersperse o $ pprint <$> xs 

-- pprintBin b o []     = b
-- pprintBin b o [x]    = pprint x
-- pprintBin b o (x:xs) = pprint x <+> o <+> pprintBin b o xs 

instance PPrint a => PPrint (PVar a) where
  pprint (PV s _ xts)     = pprint s <+> hsep (pprint <$> dargs xts)
    where 
      dargs               = map thd3 . takeWhile (\(_, x, y) -> EVar x /= nexpr y)
      nexpr (EVar (S ss)) = EVar $ stringSymbol ss
      nexpr e             = e

instance PPrint Predicate where
  pprint (Pr [])       = text "True"
  pprint (Pr pvs)      = hsep $ punctuate (text "&") (map pprint pvs)

instance PPrint Refa where
  pprint (RConc p)     = pprint p
  pprint k             = toFix k
 
instance PPrint Reft where 
  pprint r@(Reft (_,ras)) 
    | isTauto r        = text "true"
    | otherwise        = {- intersperse comma -} pprintBin trueD andD $ flattenRefas ras

instance PPrint SortedReft where
  pprint (RR so (Reft (v, ras))) 
    = braces 
    $ (pprint v) <+> (text ":") <+> (toFix so) <+> (text "|") <+> pprint ras

------------------------------------------------------------------------
-- | Error Data Type ---------------------------------------------------
------------------------------------------------------------------------

type ErrorResult = FixResult Error

data Error = 
    ErrSubType  { pos :: !SrcSpan
                , msg :: !Doc
                , act :: !SpecType
                , exp :: !SpecType
                } -- ^ liquid type error

  | ErrParse    { pos :: !SrcSpan
                , msg :: !Doc
                , err :: !ParseError
                } -- ^ specification parse error
  | ErrTySpec   { pos :: !SrcSpan
                , var :: !Doc
                , typ :: !SpecType  
                , msg :: !Doc
                } -- ^ sort error in specification
  | ErrDupSpecs { pos :: !SrcSpan
                , var :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple specs for same binder error 
  | ErrInvt     { pos :: !SrcSpan
                , inv :: !SpecType
                , msg :: !Doc
                } -- ^ Invariant sort error
  | ErrMeas     { pos :: !SrcSpan
                , ms  :: !Symbol
                , msg :: !Doc
                } -- ^ Measure sort error
  | ErrGhc      { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking
  | ErrMismatch { pos :: !SrcSpan
                , var :: !Doc
                , hs  :: !Type
                , exp :: !SpecType
                } -- ^ Mismatch between Liquid and Haskell types
  | ErrOther    {  msg :: !Doc 
                } -- ^ Unexpected PANIC 
  deriving (Typeable)

instance Eq Error where
  e1 == e2 = pos e1 == pos e2

instance Ord Error where 
  e1 <= e2 = pos e1 <= pos e2

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
  result (ErrOther d) = UnknownError d 
  result e            = result [e]

instance Result (FixResult Cinfo) where
  result = fmap cinfoError  

--------------------------------------------------------------------------------
--- Module Names
--------------------------------------------------------------------------------

data ModName = ModName !ModType !ModuleName deriving (Eq,Ord)

instance Show ModName where
  show = getModString

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

type RTBareOrSpec = Either (ModName, (RTAlias String BareType))
                           (RTAlias RTyVar SpecType)

type RTPredAlias  = Either (ModName, RTAlias Symbol Pred)
                           (RTAlias Symbol Pred)

data RTEnv   = RTE { typeAliases :: M.HashMap String RTBareOrSpec
                   , predAliases :: M.HashMap String RTPredAlias
                   }

instance Monoid RTEnv where
  (RTE ta1 pa1) `mappend` (RTE ta2 pa2) = RTE (ta1 `M.union` ta2) (pa1 `M.union` pa2)
  mempty = RTE M.empty M.empty

mapRT f e = e { typeAliases = f $ typeAliases e }
mapRP f e = e { predAliases = f $ predAliases e }

cinfoError (Ci _ (Just e)) = e
cinfoError (Ci l _)        = ErrOther $ text $ "Cinfo:" ++ (showPpr l)


--------------------------------------------------------------------------------
--- Measures
--------------------------------------------------------------------------------
-- MOVE TO TYPES
data Measure ty ctor = M { 
    name :: LocSymbol
  , sort :: ty
  , eqns :: [Def ctor]
  }

data CMeasure ty
  = CM { cName :: LocSymbol
       , cSort :: ty
       }

-- data IMeasure ty ctor
--   = IM { iName :: LocSymbol
--        , iSort :: ty
--        , iEqns :: [Def ctor]
--        }

-- MOVE TO TYPES
data Def ctor 
  = Def { 
    measure :: LocSymbol
  , ctor    :: ctor 
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Show)

-- MOVE TO TYPES
data Body 
  = E Expr          -- ^ Measure Refinement: {v | v = e } 
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  deriving (Show)

instance Subable (Measure ty ctor) where
  syms (M _ _ es)      = concatMap syms es
  substa f  (M n s es) = M n s $ substa f  <$> es
  substf f  (M n s es) = M n s $ substf f  <$> es
  subst  su (M n s es) = M n s $ subst  su <$> es

instance Subable (Def ctor) where
  syms (Def _ _ _ bd)      = syms bd
  substa f  (Def m c b bd) = Def m c b $ substa f  bd
  substf f  (Def m c b bd) = Def m c b $ substf f  bd
  subst  su (Def m c b bd) = Def m c b $ subst  su bd

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
           , rcTyVars  :: [String]
           , rcMethods :: [(LocSymbol,ty)]
           } deriving (Show)

instance Functor RClass where
  fmap f (RClass n ss tvs ms) = RClass n (fmap f ss) tvs (fmap (second f) ms)
