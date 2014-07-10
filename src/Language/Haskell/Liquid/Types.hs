{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-} 
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE DeriveGeneric         #-}

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
  , dummyLoc

  -- * Symbols
  , LocSymbol
  , LocString

  -- * Data Constructors
  , BDataCon (..)

  -- * Constructors and Destructors
  , mkArrow, bkArrowDeep, bkArrow, safeBkArrow 
  , mkUnivs, bkUniv, bkClass
  , rFun
  , Oblig(..), ignoreOblig
  , addTermCond
  , addInvCond

  , isBase

  , RTypeRep(..), fromRTypeRep, toRTypeRep

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

  -- * Inferred Annotations 
  , AnnInfo (..)
  , Annot (..)

  -- * Overall Output
  , Output (..)

  -- * Default unknown name
  , dummyName, isDummy
  -- * Refinement Hole
  , hole, isHole

  , classToRApp

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
  , PPEnv (..), ppEnv, ppEnvShort

  -- * Import handling
  , ModName (..), ModType (..), isSrcImport, isSpecImport
  , getModName, getModString

  -- * Refinement Type Aliases
  , RTEnv (..), mapRT, mapRP, RTBareOrSpec

  -- * Final Result
  , Result (..)

  -- * Different kinds of errors
  , Error (..)
  , EMsg (..)
  , LParseError (..)
  , ErrorResult
  -- , showEMsg 
  , errSpan
  , errOther

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

  -- * KV Profiling
  , KVKind (..)   -- ^ types of kvars
  , KVProf        -- ^ profile table
  , emptyKVProf   -- ^ empty profile
  , updKVProf     -- ^ extend profile

  , pappSym, pToRef, pApp

  , insertsSEnv

  , Stratum(..), Strata, isSVar, getStrata, makeDivType, makeFinType
  )
  where

import FastString                               (fsLit)
import SrcLoc                                   (noSrcSpan, mkGeneralSrcSpan, SrcSpan)
import TyCon
import DataCon
import NameSet
import Class                                    (classTyCon)
import TypeRep                          hiding  (maybeParen, pprArrowChain)  
import Var
import Unique
import Literal
import Text.Printf
import GHC                                      (Class, HscEnv, ModuleName, Name, moduleNameString)
import GHC.Generics
import Language.Haskell.Liquid.GhcMisc 

import Control.Arrow                            (second)
import Control.Monad                            (liftM, liftM2, liftM3)
import            qualified Control.Monad.Error as Ex
import Control.DeepSeq
import Control.Applicative                      ((<$>), (<*>))
import Data.Typeable                            (Typeable)
import Data.Generics                            (Data)   
import Data.Monoid                              hiding ((<>))
import qualified  Data.Foldable as F
import            Data.Hashable
import qualified  Data.HashMap.Strict as M
import qualified  Data.HashSet as S
import            Data.Function                (on)
import            Data.Maybe                   (maybeToList, fromMaybe)
import            Data.Traversable             hiding (mapM)
import            Data.List                    (isSuffixOf, nub, union, unionBy)
import            Data.Aeson        hiding     (Result)      
import Text.Parsec.Pos              (SourcePos, newPos, sourceName, sourceLine, sourceColumn) 
import Text.Parsec.Error            (ParseError) 
import Text.PrettyPrint.HughesPJ    
import Language.Fixpoint.Config     hiding (Config) 
import Language.Fixpoint.Misc
import Language.Fixpoint.Types      hiding (Predicate, Def, R)
-- import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Names      (symSepName)
import CoreSyn (CoreBind)

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
  , binders        :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , nocaseexpand   :: Bool       -- ^ disable case expand
  , strata         :: Bool       -- ^ enable strata analysis
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , totality       :: Bool       -- ^ check totality in definitions
  , noPrune        :: Bool       -- ^ disable prunning unsorted Refinements
  , maxParams      :: Int        -- ^ the maximum number of parameters to accept when mining qualifiers
  , smtsolver      :: SMTSolver  -- ^ name of smtsolver to use [default: z3-API]
  , shortNames     :: Bool       -- ^ whether to drop module qualifers from pretty-printed names
  , ghcOptions     :: [String]   -- ^ command-line options to pass to GHC
  } deriving (Data, Typeable, Show, Eq)


-----------------------------------------------------------------------------
-- | Printer ----------------------------------------------------------------
-----------------------------------------------------------------------------

class PPrint a where
  pprint :: a -> Doc

showpp :: (PPrint a) => a -> String 
showpp = render . pprint 

showEMsg :: (PPrint a) => a -> EMsg 
showEMsg = EMsg . showpp 

-- pshow :: PPrint a => a -> String
-- pshow = render . pprint

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
ppEnvCurrent    = PP False False False False
ppEnvPrintPreds = PP True False False False
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
  , meas       :: ![(Symbol, Located RefType)]   -- ^ Measure Types  
                                                 -- eg.  len :: [a] -> Int
  , invariants :: ![Located SpecType]            -- ^ Data Type Invariants

  , ialiases   :: ![(Located SpecType, Located SpecType)] -- ^ Data Type Invariant Aliases
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
  , texprs     :: ![(Var, [Expr])]               -- ^ Lexicographically ordered expressions for termination
  , lvars      :: !(S.HashSet Var)               -- ^ Variables that should be checked in the environment they are used
  , lazy       :: !(S.HashSet Var)               -- ^ Binders to IGNORE during termination checking
  , config     :: !Config                        -- ^ Configuration Options
  , exports    :: !NameSet                       -- ^ `Name`s exported by the module being verified
  , measures   :: [Measure SpecType DataCon]
  , tyconEnv   :: M.HashMap TyCon RTyCon
  }


data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![PVar RSort]
                     , freeLabelTy  :: ![Symbol]
                     , covPs        :: ![Int] -- indexes of covariant predicate arguments
                     , contravPs    :: ![Int] -- indexes of contravariant predicate arguments
                     , sizeFun      :: !(Maybe (Symbol -> Expr))
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![PVar RSort]
                         , freeLabels :: ![Symbol]
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
       , parg  :: !Symbol
       , pargs :: ![(t, Symbol, Expr)]
       }
	deriving (Generic, Data, Typeable, Show)

instance Eq (PVar t) where
  pv == pv' = pname pv == pname pv' {- UNIFY: What about: && eqArgs pv pv' -}

instance Ord (PVar t) where
  compare (PV n _ _ _)  (PV n' _ _ _) = compare n n'

instance Functor PVar where
  fmap f (PV x t v txys) = PV x (f t) v (mapFst3 f <$> txys)

instance (NFData a) => NFData (PVar a) where
  rnf (PV n t v txys) = rnf n `seq` rnf v `seq` rnf t `seq` rnf txys

instance Hashable (PVar a) where
  hashWithSalt i (PV n _ _ xys) = hashWithSalt i  n -- : (thd3 <$> xys)

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
  rnf (U r p s) = rnf r `seq` rnf p `seq` rnf s

instance NFData Strata where
  rnf _ = ()

instance NFData PrType where
  rnf _ = ()

instance NFData RTyVar where
  rnf _ = ()


-- MOVE TO TYPES
newtype RTyVar = RTV TyVar deriving (Generic, Data, Typeable)

data RTyCon = RTyCon 
  { rTyCon     :: !TyCon            -- GHC Type Constructor
  , rTyConPs   :: ![RPVar]          -- Predicate Parameters
  , rTyConInfo :: !TyConInfo        -- TyConInfo
  }
  deriving (Generic, Data, Typeable)

defaultTyConInfo = TyConInfo [] [] [] [] Nothing

instance Default TyConInfo where
  def = defaultTyConInfo


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
--  does not appear in the data definition, we enforce BOTH
--  con - contra variance

data TyConInfo = TyConInfo
  { covariantTyArgs     :: ![Int] -- ^ indexes of covariant type arguments
  , contravariantTyArgs :: ![Int] -- ^ indexes of contravariant type arguments
  , covariantPsArgs     :: ![Int] -- ^ indexes of covariant predicate arguments
  , contravariantPsArgs :: ![Int] -- ^ indexes of contravariant predicate arguments
  , sizeFunction        :: !(Maybe (Symbol -> Expr))
  } deriving (Generic, Data, Typeable)


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

  | RAllS {
      rt_sbind  :: !(Symbol)
    , rt_ty     :: !(RType p c tv r)
    }

  | RApp  { 
      rt_tycon  :: !c
    , rt_args   :: ![RType p c tv r]     
    , rt_pargs  :: ![Ref (RType p c tv ()) r (RType p c tv r)] 
    , rt_reft   :: !r
    }

  | RCls  { 
      rt_class  :: !p
    , rt_args   :: ![RType p c tv r]
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

  | RRTy  {
      rt_env   :: ![(Symbol, RType p c tv r)]
    , rt_ref   :: !r
    , rt_obl   :: !Oblig 
    , rt_ty    :: !(RType p c tv r)
    }
  | ROth  !String 

  | RHole r -- ^ let LH match against the Haskell type and add k-vars, e.g. `x:_`
            --   see tests/pos/Holes.hs
  deriving (Generic, Data, Typeable)
  
data Oblig 
  = OTerm -- ^ Obligation that proves termination
  | OInv  -- ^ Obligation that proves invariants
  deriving (Generic, Data, Typeable)

ignoreOblig (RRTy _ _ _ t) = t
ignoreOblig t              = t

instance Show Oblig where
 show OTerm = "termination-condition"
 show OInv  = "invariant-obligation"

instance PPrint Oblig where
  pprint = text . show

data Ref t s m 
  = RMono [(Symbol, t)] s
  | RPoly [(Symbol, t)] m
  deriving (Generic, Data, Typeable)

-- MOVE TO TYPES
data UReft r
  = U { ur_reft :: !r, ur_pred :: !Predicate, ur_strata :: !Strata }
    deriving (Generic, Data, Typeable)

-- MOVE TO TYPES
type BRType     = RType LocString LocString String
type RRType     = RType Class     RTyCon    RTyVar

type BSort      = BRType    ()
type RSort      = RRType    ()

type BPVar      = PVar      BSort
type RPVar      = PVar      RSort

type RReft      = UReft     Reft 
type PrType     = RRType    Predicate
type BareType   = BRType    RReft
type SpecType   = RRType    RReft 
type RefType    = RRType    Reft


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
data DataDecl   = D { tycName   :: LocString
                                -- ^ Type  Constructor Name
                    , tycTyVars :: [String]
                                -- ^ Tyvar Parameters
                    , tycPVars  :: [PVar BSort]
                                -- ^ PVar  Parameters
                    , tycTyLabs :: [String]
                                -- ^ PLabel  Parameters
                    , tycDCons  :: [(LocString, [(String, BareType)])]
                                -- ^ [DataCon, [(fieldName, fieldType)]]
                    , tycSrcPos :: !SourcePos
                                -- ^ Source Position
                    , tycSFun   :: (Maybe (Symbol -> Expr))
                                -- ^ Measure that should decrease in recursive calls
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

data RTypeRep p c tv r
  = RTypeRep { ty_vars   :: [tv]
             , ty_preds  :: [PVar (RType p c tv ())]
             , ty_labels :: [Symbol]
             , ty_binds  :: [Symbol]
             , ty_args   :: [RType p c tv r]
             , ty_res    :: (RType p c tv r)
             }

fromRTypeRep rep 
  = mkArrow (ty_vars rep) (ty_preds rep) (ty_labels rep) (zip (ty_binds rep) (ty_args rep)) (ty_res rep)

toRTypeRep :: RType p c tv r -> RTypeRep p c tv r
toRTypeRep t 
  = RTypeRep αs πs ls xs ts t''
  where (αs, πs, ls, t') = bkUniv  t
        (xs, ts, t'')    = bkArrow t'

mkArrow αs πs ls xts = mkUnivs αs πs ls . mkArrs xts 
  where 
    mkArrs xts t  = foldr (uncurry rFun) t xts 

bkArrowDeep (RAllT _ t)     = bkArrowDeep t
bkArrowDeep (RAllP _ t)     = bkArrowDeep t
bkArrowDeep (RAllS _ t)     = bkArrowDeep t
bkArrowDeep (RFun x t t' _) = let (xs, ts, t'') = bkArrowDeep t'  in (x:xs, t:ts, t'')
bkArrowDeep t               = ([], [], t)

bkArrow (RFun x t t' _) = let (xs, ts, t'') = bkArrow t'  in (x:xs, t:ts, t'')
bkArrow t               = ([], [], t)

safeBkArrow (RAllT _ _) = errorstar "safeBkArrow on RAllT"
safeBkArrow (RAllP _ _) = errorstar "safeBkArrow on RAllP"
safeBkArrow (RAllS _ t) = safeBkArrow t -- errorstar "safeBkArrow on RAllS"
-- tmp for unfoldR
-- safeBkArrow (RAllS _ _) = errorstar "safeBkArrow on RAllS"
safeBkArrow t           = bkArrow t

mkUnivs αs πs ls t = foldr RAllT (foldr RAllP (foldr RAllS t ls) πs) αs 

bkUniv :: RType t t1 a t2 -> ([a], [PVar (RType t t1 a ())], [Symbol], RType t t1 a t2)
bkUniv (RAllT α t)      = let (αs, πs, ls, t') = bkUniv t in  (α:αs, πs, ls, t') 
bkUniv (RAllP π t)      = let (αs, πs, ls, t') = bkUniv t in  (αs, π:πs, ls, t') 
bkUniv (RAllS s t)      = let (αs, πs, ss, t') = bkUniv t in  (αs, πs, s:ss, t') 
bkUniv t                = ([], [], [], t)

bkClass (RFun _ (RCls c t) t' _) = let (cs, t'') = bkClass t' in ((c, t):cs, t'')
bkClass t                        = ([], t)

rFun b t t' = RFun b t t' mempty



addTermCond = addObligation OTerm

addInvCond :: SpecType -> RReft -> SpecType
addInvCond t r' 
  | null rv 
  = t
  | otherwise
  = fromRTypeRep $ trep {ty_res = RRTy [(x', tbd)] r OInv tbd}
  where trep = toRTypeRep t
        tbd  = ty_res trep
        r    = r'{ur_reft = Reft (v, rx)}
        su   = (v, EVar x')
        x'   = stringSymbol "xInv"
        rx   = [RConc $ PIff (PBexp $ EVar v) $ subst1 r su | RConc r <- rv]

        Reft(v, rv) = ur_reft r'

addObligation :: Oblig -> SpecType -> RReft -> SpecType
addObligation o t r = mkArrow αs πs ls xts $ RRTy [] r o t2
  where (αs, πs, ls, t1) = bkUniv t
        (xs, ts, t2)     = bkArrow t1
        xts              = zip xs ts

--------------------------------------------

instance Subable Stratum where
  syms (SVar s) = [s]
  syms _        = []
  subst su (SVar s) = SVar $ subst su s
  subst su s        = s
  substf f (SVar s) = SVar $ substf f s
  substf f s        = s
  substa f (SVar s) = SVar $ substa f s
  substa f s        = s

instance Subable Strata where
  syms s     = concatMap syms s
  subst su   = (subst su <$>)
  substf f   = (substf f <$>)
  substa f   = (substa f <$>)

instance Reftable Strata where
  isTauto []         = True
  isTauto _          = False

  ppTy s             = error "ppTy on Strata" 
  toReft s           = mempty
  params s           = [l | SVar l <- s]
  bot s              = []
  top s              = []

instance (PPrint r, Reftable r) => Reftable (UReft r) where
  isTauto            = isTauto_ureft 
  -- ppTy (U r p) d     = ppTy r (ppTy p d) 
  ppTy               = ppTy_ureft
  toReft (U r ps _)  = toReft r `meet` toReft ps
  params (U r _ _)   = params r
  bot (U r _ s)      = U (bot r) (Pr []) (bot s)
  top (U r p s)      = U (top r) (top p) (top s)

isTauto_ureft u      = isTauto (ur_reft u) && isTauto (ur_pred u) && (isTauto $ ur_strata u)

isTauto_ureft' u     = isTauto (ur_reft u) && isTauto (ur_pred u)

ppTy_ureft u@(U r p s) d 
  | isTauto_ureft  u  = d
  | isTauto_ureft' u  = d <> ppr_str s
  | otherwise         = ppr_reft r (ppTy p d) s

ppr_reft r d s       = braces (toFix v <+> colon <+> d <> ppr_str s <+> text "|" <+> pprint r')
  where 
    r'@(Reft (v, _)) = toReft r

ppr_str [] = empty
ppr_str s  = text "^" <> pprint s

instance Subable r => Subable (UReft r) where
  syms (U r p s)     = syms r ++ syms p 
  subst s (U r z l)  = U (subst s r) (subst s z) (subst s l)
  substf f (U r z l) = U (substf f r) (substf f z) (substf f l) 
  substa f (U r z l) = U (substa f r) (substa f z) (substa f l)
 
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
  
  toReft (Pr ps@(p:_))        = Reft (parg p, pToRef <$> ps)
  toReft _                    = mempty
  params                      = errorstar "TODO: instance of params for Predicate"


pToRef p = RConc $ pApp (pname p) $ (EVar $ parg p) : (thd3 <$> pargs p)

pApp      :: Symbol -> [Expr] -> Pred
pApp p es = PBexp $ EApp (dummyLoc $ pappSym $ length es) (EVar p:es)

pappSym n  = S $ "papp" ++ show n

---------------------------------------------------------------
--------------------------- Visitors --------------------------
---------------------------------------------------------------

isTrivial t = foldReft (\r b -> isTauto r && b) True t

instance Functor UReft where
  fmap f (U r p s) = U (f r) p s

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
emapReft f γ (RAllS p t)         = RAllS p (emapReft f γ t)
emapReft f γ (RFun x t t' r)     = RFun  x (emapReft f γ t) (emapReft f (x:γ) t') (f γ r)
emapReft f γ (RApp c ts rs r)    = RApp  c (emapReft f γ <$> ts) (emapRef f γ <$> rs) (f γ r)
emapReft f γ (RCls c ts)         = RCls  c (emapReft f γ <$> ts) 
emapReft f γ (RAllE z t t')      = RAllE z (emapReft f γ t) (emapReft f γ t')
emapReft f γ (REx z t t')        = REx   z (emapReft f γ t) (emapReft f γ t')
emapReft _ _ (RExprArg e)        = RExprArg e
emapReft f γ (RAppTy t t' r)     = RAppTy (emapReft f γ t) (emapReft f γ t') (f γ r)
emapReft f γ (RRTy e r o t)      = RRTy  (mapSnd (emapReft f γ) <$> e) (f γ r) o (emapReft f γ t)
emapReft _ _ (ROth s)            = ROth  s 
emapReft f γ (RHole r)           = RHole (f γ r)

emapRef :: ([Symbol] -> t -> s) ->  [Symbol] -> Ref (RType p c tv ()) t (RType p c tv t) -> Ref (RType p c tv ()) s (RType p c tv s)
emapRef  f γ (RMono s r)         = RMono s $ f γ r
emapRef  f γ (RPoly s t)         = RPoly s $ emapReft f γ t

------------------------------------------------------------------------------------------------------
-- isBase' x t = traceShow ("isBase: " ++ showpp x) $ isBase t

-- isBase :: RType a -> Bool
isBase (RAllP _ t)      = isBase t
isBase (RVar _ _)       = True
isBase (RApp _ ts _ _)  = all isBase ts
isBase (RFun _ t1 t2 _) = isBase t1 && isBase t2
isBase (RAppTy t1 t2 _) = isBase t1 && isBase t2
isBase (RRTy _ _ _ t)   = isBase t
isBase _                = False


mapReftM :: (Monad m) => (r1 -> m r2) -> RType p c tv r1 -> m (RType p c tv r2)
mapReftM f (RVar α r)         = liftM   (RVar  α)   (f r)
mapReftM f (RAllT α t)        = liftM   (RAllT α)   (mapReftM f t)
mapReftM f (RAllP π t)        = liftM   (RAllP π)   (mapReftM f t)
mapReftM f (RAllS s t)        = liftM   (RAllS s)   (mapReftM f t)
mapReftM f (RFun x t t' r)    = liftM3  (RFun x)    (mapReftM f t)          (mapReftM f t')       (f r)
mapReftM f (RApp c ts rs r)   = liftM3  (RApp  c)   (mapM (mapReftM f) ts)  (mapM (mapRefM f) rs) (f r)
mapReftM f (RCls c ts)        = liftM   (RCls  c)   (mapM (mapReftM f) ts) 
mapReftM f (RAllE z t t')     = liftM2  (RAllE z)   (mapReftM f t)          (mapReftM f t')
mapReftM f (REx z t t')       = liftM2  (REx z)     (mapReftM f t)          (mapReftM f t')
mapReftM _ (RExprArg e)       = return  $ RExprArg e 
mapReftM f (RAppTy t t' r)    = liftM3  RAppTy (mapReftM f t) (mapReftM f t') (f r)
mapReftM _ (ROth s)           = return  $ ROth  s 
mapReftM f (RHole r)          = liftM   RHole       (f r)

mapRefM  :: (Monad m) => (t -> m s) -> Ref (RType p c tv ()) t (RType p c tv t) -> m (Ref (RType p c tv ()) s (RType p c tv s))
mapRefM  f (RMono s r)        = liftM   (RMono s)      (f r)
mapRefM  f (RPoly s t)        = liftM   (RPoly s)      (mapReftM f t)

-- foldReft :: (r -> a -> a) -> a -> RType p c tv r -> a
foldReft f = efoldReft (\_ _ -> []) (\_ -> ()) (\_ _ -> f) (\_ γ -> γ) emptySEnv 

-- efoldReft :: Reftable r =>(p -> [RType p c tv r] -> [(Symbol, a)])-> (RType p c tv r -> a)-> (SEnv a -> Maybe (RType p c tv r) -> r -> c1 -> c1)-> SEnv a-> c1-> RType p c tv r-> c1
efoldReft cb g f fp = go 
  where
    -- folding over RType 
    go γ z me@(RVar _ r)                = f γ (Just me) r z 
    go γ z (RAllT _ t)                  = go γ z t
    go γ z (RAllP p t)                  = go (fp p γ) z t
    go γ z (RAllS s t)                  = go γ z t
    go γ z me@(RFun _ (RCls c ts) t' r) = f γ (Just me) r (go (insertsSEnv γ (cb c ts)) (go' γ z ts) t') 
    go γ z me@(RFun x t t' r)           = f γ (Just me) r (go (insertSEnv x (g t) γ) (go γ z t) t')
    go γ z me@(RApp _ ts rs r)          = f γ (Just me) r (ho' γ (go' (insertSEnv (rTypeValueVar me) (g me) γ) z ts) rs)
    
    go γ z (RCls c ts)                  = go' γ z ts
    go γ z (RAllE x t t')               = go (insertSEnv x (g t) γ) (go γ z t) t' 
    go γ z (REx x t t')                 = go (insertSEnv x (g t) γ) (go γ z t) t' 
    go _ z (ROth _)                     = z 
    go γ z me@(RRTy e r o t)            = f γ (Just me) r (go γ z t)
    go γ z me@(RAppTy t t' r)           = f γ (Just me) r (go γ (go γ z t) t')
    go _ z (RExprArg _)                 = z
    go γ z me@(RHole r)                 = f γ (Just me) r z

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
-- efoldRef g f γ z (RPoly ss t)         = efoldReft g f (insertsSEnv γ ((mepSnd (g . ofRSort)) <$> ss)) z t

mapBot f (RAllT α t)       = RAllT α (mapBot f t)
mapBot f (RAllP π t)       = RAllP π (mapBot f t)
mapBot f (RAllS s t)       = RAllS s (mapBot f t)
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
mapBind f (RAllS s t)      = RAllS s (mapBind f t)
mapBind f (RFun b t1 t2 r) = RFun (f b)  (mapBind f t1) (mapBind f t2) r
mapBind f (RApp c ts rs r) = RApp c (mapBind f <$> ts) (mapBindRef f <$> rs) r
mapBind f (RCls c ts)      = RCls c (mapBind f <$> ts)
mapBind f (RAllE b t1 t2)  = RAllE  (f b) (mapBind f t1) (mapBind f t2)
mapBind f (REx b t1 t2)    = REx    (f b) (mapBind f t1) (mapBind f t2)
mapBind _ (RVar α r)       = RVar α r
mapBind _ (ROth s)         = ROth s
mapBind _ (RHole r)        = RHole r
mapBind f (RRTy e r o t)   = RRTy e r o (mapBind f t)
mapBind _ (RExprArg e)     = RExprArg e
mapBind f (RAppTy t t' r)  = RAppTy (mapBind f t) (mapBind f t') r

mapBindRef f (RMono s r)   = RMono (mapFst f <$> s) r
mapBindRef f (RPoly s t)   = RPoly (mapFst f <$> s) $ mapBind f t


--------------------------------------------------
ofRSort ::  Reftable r => RType p c tv () -> RType p c tv r 
ofRSort = fmap mempty

toRSort :: RType p c tv r -> RType p c tv () 
toRSort = stripQuantifiers . mapBind (const dummySymbol) . fmap (const ())

stripQuantifiers (RAllT α t)      = RAllT α (stripQuantifiers t)
stripQuantifiers (RAllP _ t)      = stripQuantifiers t
stripQuantifiers (RAllS _ t)      = stripQuantifiers t
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
mapRBase f t                = t



makeLType :: Stratum -> SpecType -> SpecType
makeLType l t = fromRTypeRep trep{ty_res = mapRBase f $ ty_res trep}
  where trep = toRTypeRep t
        f (U r p s) = U r p [l]


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
  pprint (ESym s)        = pprint s

instance PPrint SymConst where
  pprint (SL s)          = text s

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
  pprint (PV s _ _ xts)   = pprint s <+> hsep (pprint <$> dargs xts)
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

newtype EMsg     = EMsg String deriving (Generic, Data, Typeable)


instance PPrint EMsg where
  pprint (EMsg s) = text s

-- | In the below, we use EMsg instead of, say, SpecType because the latter is
-- impossible to serialize, as it contains GHC internals like TyCon and Class
-- inside it.

-- | INVARIANT : all Error constructors should hava a pos field

data Error = 
    ErrSubType  { pos :: !SrcSpan
                , msg :: !Doc 
                , act :: !SpecType
                , exp :: !SpecType
                } -- ^ liquid type error

   | ErrAssType { pos :: !SrcSpan
                , obl :: !Oblig
                , msg :: !Doc
                , ref :: !RReft
                } -- ^ liquid type error

  | ErrParse    { pos :: !SrcSpan
                , msg :: !Doc
                , err :: !LParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: !SrcSpan
                , var :: !Doc
                , typ :: !SpecType  
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

  | ErrInvt     { pos :: !SrcSpan
                , inv :: !SpecType
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: !SrcSpan
                , inv :: !SpecType
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: !SrcSpan
                , t1  :: !SpecType
                , t2  :: !SpecType
                , msg :: !Doc
                } -- ^ Incompatible using error

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

  | ErrSaved    { pos :: !SrcSpan 
                , msg :: !Doc
                } -- ^ Unexpected PANIC 
 
  | ErrOther    { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ Unexpected PANIC 
  deriving (Typeable)

data LParseError = LPE !SourcePos [String] 
                   deriving (Data, Typeable, Generic)


instance Eq Error where
  e1 == e2 = pos e1 == pos e2

instance Ord Error where 
  e1 <= e2 = pos e1 <= pos e2

instance Ex.Error Error where
  strMsg = errOther . pprint

errSpan :: Error -> SrcSpan
errSpan = pos 

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
cinfoError (Ci l _)        = errOther $ text $ "Cinfo:" ++ showPpr l


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

-- MOVE TO TYPES
data Def ctor 
  = Def { 
    measure :: LocSymbol
  , ctor    :: ctor 
  , binds   :: [Symbol]
  , body    :: Body
  } deriving (Show)
  
deriving instance (Eq ctor) => Eq (Def ctor)

-- MOVE TO TYPES
data Body 
  = E Expr          -- ^ Measure Refinement: {v | v = e } 
  | P Pred          -- ^ Measure Refinement: {v | (? v) <=> p }
  | R Symbol Pred   -- ^ Measure Refinement: {v | p}
  deriving (Show, Eq)

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


------------------------------------------------------------------------
-- | Annotations -------------------------------------------------------
------------------------------------------------------------------------

newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe String, a)]) deriving (Generic)

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
  rnf (AI x) = () 

instance NFData (Annot a) where
  rnf (AnnDef x) = ()
  rnf (AnnRDf x) = ()
  rnf (AnnUse x) = ()
  rnf (AnnLoc x) = ()

------------------------------------------------------------------------
-- | Output ------------------------------------------------------------
------------------------------------------------------------------------

data Output a = O { o_vars   :: Maybe [String] 
                  , o_warns  :: [String]
                  , o_types  :: !(AnnInfo a)
                  , o_templs :: !(AnnInfo a)
                  , o_bots   :: ![SrcSpan] 
                  , o_result :: FixResult Error
                  } deriving (Generic)

emptyOutput = O Nothing [] mempty mempty [] mempty

instance Monoid (Output a) where 
  mempty        = emptyOutput  
  mappend o1 o2 = O { o_vars   = sortNub <$> mappend (o_vars   o1) (o_vars   o2)
                    , o_warns  = sortNub  $  mappend (o_warns  o1) (o_warns  o2)
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

updKVProf :: KVKind -> [Symbol] -> KVProf -> KVProf 
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

hole = RKvar (S "HOLE") mempty

isHole (toReft -> (Reft (_, [RKvar (S "HOLE") _]))) = True
isHole _                                            = False


classToRApp :: SpecType -> SpecType
classToRApp (RCls cl ts) 
  = RApp (RTyCon (classTyCon cl) def def) ts mempty mempty

instance Symbolic DataCon where
  symbol = symbol . dataConWorkId

instance Symbolic Var where
  symbol = varSymbol

varSymbol ::  Var -> Symbol
varSymbol v 
  | us `isSuffixOf` vs = stringSymbol vs  
  | otherwise          = stringSymbol $ vs ++ [symSepName] ++ us
  where us  = showPpr $ getDataConVarUnique v
        vs  = showPpr v

instance PPrint DataCon where
  pprint = text . showPpr

instance Show DataCon where
  show = showpp
