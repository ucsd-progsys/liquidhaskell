--------------------------------------------------------------------------------
-- | Command Line Config Options -----------------------------------------------
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.UX.Config (
   -- * Configuration Options
     Config (..)
   , HasConfig (..)
   , hasOpt
   , totalityCheck
   , terminationCheck

   , Instantiate (..)
   , allowSMTInstationation
   , allowLiquidInstationation
   , allowLiquidInstationationGlobal
   , allowLiquidInstationationLocal

   , ProofMethod (..)
   , allowRewrite
   , allowArithmetic 
   ) where

import Prelude hiding (error)

import Data.Serialize ( Serialize )
import Language.Fixpoint.Types.Config hiding (Config)
-- import Data.Typeable  (Typeable)
-- import Data.Generics  (Data)
import GHC.Generics

import System.Console.CmdArgs


totalityCheck :: Config -> Bool
totalityCheck config
  = totality config || totalHaskell config

terminationCheck :: Config -> Bool
terminationCheck config
  = totalHaskell config || not (notermination config)


-- NOTE: adding strictness annotations breaks the help message
data Config = Config {
    files          :: [FilePath] -- ^ source files to check
  , idirs          :: [FilePath] -- ^ path to directory for including specs
  , diffcheck      :: Bool       -- ^ check subset of binders modified (+ dependencies) since last check
  , linear         :: Bool       -- ^ uninterpreted integer multiplication and division
  , stringTheory   :: Bool       -- ^ interpretation of string theory in the logic
  , higherorder    :: Bool       -- ^ allow higher order binders into the logic
  , higherorderqs  :: Bool       -- ^ allow higher order qualifiers
  , extensionality :: Bool       -- ^ allow function extentionality axioms
  , alphaEquivalence :: Bool     -- ^ allow lambda alpha-equivalence axioms
  , betaEquivalence  :: Bool     -- ^ allow lambda beta-equivalence axioms
  , normalForm     :: Bool       -- ^ allow lambda normalization-equivalence axioms
  , fullcheck      :: Bool       -- ^ check all binders (overrides diffcheck)
  , saveQuery      :: Bool       -- ^ save fixpoint query
  , checks         :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , gradual        :: Bool       -- ^ enable gradual type checking 
  , totalHaskell   :: Bool       -- ^ Check for termination and totality, Overrides no-termination flags
  , autoproofs     :: Bool       -- ^ automatically construct proofs from axioms
  , nowarnings     :: Bool       -- ^ disable warnings output (only show errors)
  , noannotations  :: Bool       -- ^ disable creation of intermediate annotation files
  , trustInternals :: Bool       -- ^ type all internal variables with true
  , nocaseexpand   :: Bool       -- ^ disable case expand
  , strata         :: Bool       -- ^ enable strata analysis
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , totality       :: Bool       -- ^ check totality in definitions
  , pruneUnsorted  :: Bool       -- ^ enable prunning unsorted Refinements
  , cores          :: Maybe Int  -- ^ number of cores used to solve constraints
  , minPartSize    :: Int        -- ^ Minimum size of a partition
  , maxPartSize    :: Int        -- ^ Maximum size of a partition. Overrides minPartSize
  , maxParams      :: Int        -- ^ the maximum number of parameters to accept when mining qualifiers
  , smtsolver      :: Maybe SMTSolver  -- ^ name of smtsolver to use [default: try z3, cvc4, mathsat in order]
  , shortNames     :: Bool       -- ^ drop module qualifers from pretty-printed names.
  , shortErrors    :: Bool       -- ^ don't show subtyping errors and contexts.
  , cabalDir       :: Bool       -- ^ find and use .cabal file to include paths to sources for imported modules
  , ghcOptions     :: [String]   -- ^ command-line options to pass to GHC
  , cFiles         :: [String]   -- ^ .c files to compile and link against (for GHC)
  , eliminate      :: Eliminate  -- ^ eliminate (i.e. don't use qualifs for) for "none", "cuts" or "all" kvars
  -- , noEliminate    :: Bool       -- ^ don't eliminate non-top-level and non-recursive KVars
  --, oldEliminate   :: Bool       -- ^ use old eliminate algorithm (for benchmarking only)
  , port           :: Int        -- ^ port at which lhi should listen
  , exactDC        :: Bool       -- ^ Automatically generate singleton types for data constructors
  , noMeasureFields :: Bool      -- ^ Do not automatically lift data constructor fields into measures
  , scrapeImports   :: Bool      -- ^ scrape qualifiers from imported specifications
  , scrapeInternals :: Bool      -- ^ scrape qualifiers from auto specifications
  , scrapeUsedImports  :: Bool   -- ^ scrape qualifiers from used, imported specifications
  , elimStats       :: Bool       -- ^ print eliminate stats
  , elimBound       :: Maybe Int  -- ^ eliminate upto given depth of KVar chains
  , json            :: Bool       -- ^ print results (safe/errors) as JSON
  , counterExamples :: Bool       -- ^ attempt to generate counter-examples to type errors
  , timeBinds       :: Bool       -- ^ check and time each (asserted) type-sig separately
  , noPatternInline :: Bool       -- ^ treat code patterns (e.g. e1 >>= \x -> e2) specially for inference
  , untidyCore      :: Bool       -- ^ print full blown core (with untidy names) in verbose mode
  , noSimplifyCore  :: Bool       -- ^ simplify GHC core before constraint-generation
  , nonLinCuts      :: Bool       -- ^ treat non-linear kvars as cuts
  , autoInstantiate :: Instantiate -- ^ How to instantiate axioms
  , proofMethod     :: ProofMethod -- ^ How to create automatic instances 
  , fuel            :: Int         -- ^ Fuel for axiom instantiation 
  , debugInstantionation :: Bool   -- ^ Debug Instantiation  
  } deriving (Generic, Data, Typeable, Show, Eq)

instance Serialize ProofMethod
instance Serialize Instantiate
instance Serialize SMTSolver
instance Serialize Config

data Instantiate = NoInstances | SMTInstances | LiquidInstances | LiquidInstancesLocal
  deriving (Eq, Data, Typeable, Generic)

data ProofMethod = Arithmetic | Rewrite | AllMethods 
  deriving (Eq, Data, Typeable, Generic)


allowSMTInstationation, allowLiquidInstationation, allowLiquidInstationationLocal, allowLiquidInstationationGlobal :: Config -> Bool 
allowSMTInstationation    cfg = autoInstantiate cfg == SMTInstances

allowLiquidInstationation cfg =  autoInstantiate cfg == LiquidInstances
                              || autoInstantiate cfg == LiquidInstancesLocal 

allowLiquidInstationationGlobal cfg = autoInstantiate cfg == LiquidInstances
allowLiquidInstationationLocal  cfg = autoInstantiate cfg == LiquidInstancesLocal

allowRewrite, allowArithmetic :: Config -> Bool 
allowRewrite    cfg = proofMethod cfg == Rewrite    || proofMethod cfg == AllMethods
allowArithmetic cfg = proofMethod cfg == Arithmetic || proofMethod cfg == AllMethods



instance Default ProofMethod where
  def = Rewrite

instance Show ProofMethod where
  show Arithmetic = "arithmetic"
  show Rewrite    = "rewrite"
  show AllMethods = "all"  


instance Default Instantiate where
  def = NoInstances

instance Show Instantiate where
  show NoInstances           = "none"
  show SMTInstances          = "SMT"
  show LiquidInstancesLocal  = "liquid-local"  
  show LiquidInstances       = "liquid-global"  


class HasConfig t where
  getConfig :: t -> Config

  patternFlag :: t -> Bool
  patternFlag = not . noPatternInline . getConfig

  higherOrderFlag :: t -> Bool
  higherOrderFlag = higherorder . getConfig




hasOpt :: HasConfig t => t -> (Config -> Bool) -> Bool
hasOpt t f = f (getConfig t)

instance HasConfig Config where
  getConfig = id
