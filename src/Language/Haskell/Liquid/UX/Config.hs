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
   ) where

import Prelude hiding (error)

import Data.Serialize ( Serialize )
import Language.Fixpoint.Types.Config hiding (Config)
import Data.Typeable  (Typeable)
import Data.Generics  (Data)
import GHC.Generics

-- NOTE: adding strictness annotations breaks the help message
data Config = Config {
    files          :: [FilePath] -- ^ source files to check
  , idirs          :: [FilePath] -- ^ path to directory for including specs
  , newcheck       :: Bool       -- ^ new liquid-fixpoint sort check
  , diffcheck      :: Bool       -- ^ check subset of binders modified (+ dependencies) since last check
  , linear         :: Bool       -- ^ uninterpreted integer multiplication and division
  , higherorder    :: Bool       -- ^ allow higher order binders into the logic
  , higherorderqs  :: Bool       -- ^ allow higher order qualifiers
  , fullcheck      :: Bool       -- ^ check all binders (overrides diffcheck)
  , saveQuery      :: Bool       -- ^ save fixpoint query
  , checks         :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , autoproofs     :: Bool       -- ^ automatically construct proofs from axioms
  , nowarnings     :: Bool       -- ^ disable warnings output (only show errors)
  , trustinternals :: Bool       -- ^ type all internal variables with true
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
  , noEliminate    :: Bool       -- ^ eliminate non-top-level and non-recursive KVars
  , port           :: Int        -- ^ port at which lhi should listen
  , exactDC        :: Bool       -- ^ Automatically generate singleton types for data constructors
  , scrapeImports  :: Bool       -- ^ scrape qualifiers from imported specifications
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
  } deriving (Generic, Data, Typeable, Show, Eq)

instance Serialize SMTSolver
instance Serialize Config


class HasConfig t where
  getConfig :: t -> Config

hasOpt :: HasConfig t => t -> (Config -> Bool) -> Bool
hasOpt t f = f (getConfig t)

instance HasConfig Config where
  getConfig = id
