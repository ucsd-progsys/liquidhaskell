{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{- LANGUAGE OverlappingInstances, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables, NoMonomorphismRestriction, , UndecidableInstances, , TupleSections, RankNTypes, GADTs -}


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
  
  -- * Default unknown position
  , dummyPos

  -- * All these should be MOVE TO TYPES
  , RTyVar (..), RType (..), RRType, BRType, RTyCon(..)
  , TyConable (..), RefTypable (..), SubsTy (..), Ref(..)
  , RTAlias (..)
  , BSort, BPVar, BareType, RSort, UsedPVar, RPVar, RReft, RefType
  , PrType, SpecType
  , PVar (..) , Predicate (..), UReft(..), DataDecl (..), TyConInfo(..)
  , TyConP (..), DataConP (..)

  -- * Default unknown name
  , dummyName, isDummy
  )
  where

import TyCon
import DataCon
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Var
import Literal
import Text.Printf
import GHC                          (Class, HscEnv)

import Control.DeepSeq
import Control.Applicative          ((<$>))
import Data.Typeable                (Typeable)
import Data.Generics                (Data)   
import Data.Foldable
import Data.Hashable
import Data.Traversable
import Text.Parsec.Pos              (SourcePos, newPos) 
import Text.PrettyPrint.HughesPJ    
import Language.Fixpoint.Types hiding (Predicate) 
import Language.Fixpoint.Misc

import CoreSyn (CoreBind)
import Var
-----------------------------------------------------------------------------
-- | Command Line Config Options --------------------------------------------
-----------------------------------------------------------------------------

data Config = Config { 
    files :: [FilePath] -- ^ source files to check
  , idirs :: [FilePath] -- ^ path to directory for including specs
  , binds :: ![String]  -- ^ top-level binders to check (empty means check ALL) 
  , noCheckUnknown :: Bool -- ^ whether to complain about specifications for unexported and unused values
  } deriving (Data, Typeable, Show, Eq)


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

dummyPos = newPos "?" 0 0 

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

instance Foldable Located where
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
  , ctor       :: ![(Var, Located SpecType)]     -- ^ Data Constructor Measure Sigs 
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
  , tgtVars  :: !TargetVars                      -- ^ Top-level Binders To Verify (empty means ALL binders)
  
  }
  
data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar RSort)]
                     , covPs        :: ![Int] -- indexes of covariant predicate arguments
                     , contravPs    :: ![Int] -- indexes of contravariant predicate arguments
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar RSort)]
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

instance NFData r => NFData (UReft r) where
  rnf (U r p) = rnf r `seq` rnf p

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()


-- MOVE TO TYPES
newtype RTyVar = RTV TyVar

data RTyCon = RTyCon 
  { rTyCon     :: !TyCon         -- GHC Type Constructor
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
-- data Foo a b c <p :: b -> Prop, q :: Int -> Prop, r :: a -> Prop>
--   = F (a<r> -> b<p>) | Q (c -> a) | G (Int<q> -> a<r>)
-- there will be 
--  covariantTyArgs     = [0, 1], for type arguments a and b
--  contravariantTyArgs = [0, 2], for type arguments a and c
--  covariantPsArgs     = [0, 2], for predicate arguments p and r
--  contravariantPsArgs = [1, 2], for predicate arguments q and r


data TyConInfo = TyConInfo
  { covariantTyArgs     :: ![Int] -- indexes of covariant type arguments
  , contravariantTyArgs :: ![Int] -- indexes of contravariant type arguments
  , covariantPsArgs     :: ![Int] -- indexes of covariant predicate arguments
  , contravariantPsArgs :: ![Int] -- indexes of contravariant predicate arguments
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
    , rt_allarg  :: !(RType p c tv r) 
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
class ( Fixpoint p
      , TyConable c
      , Eq p, Eq c, Eq tv
      , Hashable tv
      , Fixpoint tv
      , Reftable r
      ) => RefTypable p c tv r 
  where
    ppCls    :: p -> [RType p c tv r] -> Doc
    ppRType  :: Prec -> RType p c tv r -> Doc 
    -- ppRType  = ppr_rtype True -- False 



-- | Data type refinements

-- MOVE TO TYPES
data DataDecl   = D { tycName   :: String                           -- ^ Type  Constructor Name 
                    , tycTyVars :: [String]                         -- ^ Tyvar Parameters
                    , tycPVars  :: [PVar BSort]                     -- ^ PVar  Parameters
                    , tycDCons  :: [(String, [(String, BareType)])] -- ^ [DataCon, [(fieldName, fieldType)]]   
                    }
     --              deriving (Show) 

-- | Refinement Type Aliases

-- MOVE TO TYPES
data RTAlias tv ty 
  = RTA { rtName  :: String
        , rtTArgs :: [tv]
        , rtVArgs :: [tv] 
        , rtBody  :: ty  
        , srcPos  :: SourcePos 
        } 


