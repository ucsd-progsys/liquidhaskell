-- | Command Line Configuration Options ----------------------------------------

{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.UX.Config (
     Config (..)
   , HasConfig (..)
   , allowPLE, allowLocalPLE, allowGlobalPLE
   , patternFlag
   , higherOrderFlag
   , pruneFlag
   , maxCaseExpand 
   , exactDCFlag
   , hasOpt
   , totalityCheck
   , terminationCheck 
   , structuralTerm
   ) where

import Prelude hiding (error)
import Data.Serialize ( Serialize )
import Language.Fixpoint.Types.Config hiding (Config)
-- import qualified Language.Fixpoint.Types as F
import GHC.Generics
import System.Console.CmdArgs

-- NOTE: adding strictness annotations breaks the help message
data Config = Config 
  { files          :: [FilePath] -- ^ source files to check
  , idirs          :: [FilePath] -- ^ path to directory for including specs
  , diffcheck      :: Bool       -- ^ check subset of binders modified (+ dependencies) since last check
  , linear         :: Bool       -- ^ uninterpreted integer multiplication and division
  , stringTheory   :: Bool       -- ^ interpretation of string theory in the logic
  , higherorder    :: Bool       -- ^ allow higher order binders into the logic
  , higherorderqs  :: Bool       -- ^ allow higher order qualifiers
  , smtTimeout     :: Maybe Int  -- ^ smt timeout 
  , fullcheck      :: Bool       -- ^ check all binders (overrides diffcheck)
  , saveQuery      :: Bool       -- ^ save fixpoint query
  , checks         :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , rankNTypes     :: Bool       -- ^ Adds precise reasoning on presence of rankNTypes
  , noclasscheck   :: Bool       -- ^ disable checking class instances 
  -- , structuralTerm :: Bool       -- ^ use structural termination checker
  , nostructuralterm :: Bool    -- ^ disable structural termination check
  , gradual        :: Bool       -- ^ enable gradual type checking
  , gdepth         :: Int        -- ^ depth of gradual concretization
  , ginteractive   :: Bool       -- ^ interactive gradual solving
  , totalHaskell   :: Bool       -- ^ Check for termination and totality, Overrides no-termination flags
  , nowarnings     :: Bool       -- ^ disable warnings output (only show errors)
  , noannotations  :: Bool       -- ^ disable creation of intermediate annotation files
  , checkDerived   :: Bool       -- ^ check internal (GHC-derived) binders 
  , caseExpandDepth :: Int       -- ^ maximum case expand nesting depth. 
  , strata         :: Bool       -- ^ enable strata analysis
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , nototality     :: Bool       -- ^ disable totality check in definitions
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
  , port           :: Int        -- ^ port at which lhi should listen
  , exactDC        :: Bool       -- ^ Automatically generate singleton types for data constructors
  , noADT           :: Bool      -- ^ Disable ADTs (only used with exactDC)
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
  -- PLE-OPT , autoInstantiate :: Instantiate -- ^ How to instantiate axioms
  , noslice         :: Bool        -- ^ Disable non-concrete KVar slicing
  , noLiftedImport  :: Bool        -- ^ Disable loading lifted specifications (for "legacy" libs)
  , proofLogicEval  :: Bool        -- ^ Enable proof-by-logical-evaluation
  , proofLogicEvalLocal  :: Bool   -- ^ Enable proof-by-logical-evaluation locally, per function
  , reflection      :: Bool        -- ^ Allow "reflection"; switches on "--higherorder" and "--exactdc"
  , compileSpec     :: Bool        -- ^ Only "compile" the spec -- into .bspec file -- don't do any checking. 
  , noCheckImports  :: Bool        -- ^ Do not check the transitive imports  
  , typedHoles      :: Bool        -- ^ Warn about "typed-holes"
  } deriving (Generic, Data, Typeable, Show, Eq)

instance Serialize SMTSolver
instance Serialize Config

allowPLE :: Config -> Bool
allowPLE cfg
  =  allowGlobalPLE cfg 
  || allowLocalPLE cfg

allowGlobalPLE :: Config -> Bool
allowGlobalPLE cfg = proofLogicEval  cfg

allowLocalPLE :: Config -> Bool
allowLocalPLE cfg = proofLogicEvalLocal  cfg

instance HasConfig  Config where
  getConfig x = x

class HasConfig t where
  getConfig :: t -> Config

patternFlag :: (HasConfig t) => t -> Bool
patternFlag = not . noPatternInline . getConfig

higherOrderFlag :: (HasConfig t) => t -> Bool
higherOrderFlag x = higherorder cfg || reflection cfg 
  where 
    cfg           = getConfig x

exactDCFlag :: (HasConfig t) => t -> Bool
exactDCFlag x = exactDC cfg || reflection cfg 
  where 
    cfg       = getConfig x

pruneFlag :: (HasConfig t) => t -> Bool
pruneFlag = pruneUnsorted . getConfig

maxCaseExpand :: (HasConfig t) => t -> Int 
maxCaseExpand = caseExpandDepth . getConfig

hasOpt :: (HasConfig t) => t -> (Config -> Bool) -> Bool
hasOpt t f = f (getConfig t)

totalityCheck :: (HasConfig t) => t -> Bool
totalityCheck = totalityCheck' . getConfig

terminationCheck :: (HasConfig t) => t -> Bool
terminationCheck = terminationCheck' . getConfig

totalityCheck' :: Config -> Bool
totalityCheck' cfg = (not (nototality cfg)) || totalHaskell cfg

terminationCheck' :: Config -> Bool
terminationCheck' cfg = (totalHaskell cfg || not (notermination cfg)) 

structuralTerm :: (HasConfig a) => a -> Bool 
structuralTerm = not . nostructuralterm . getConfig

