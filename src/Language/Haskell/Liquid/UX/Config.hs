-----------------------------------------------------------------------------
-- | Command Line Config Options --------------------------------------------
-----------------------------------------------------------------------------


{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.UX.Config (

   -- * Configuration Options
     Config (..)

   ) where

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
  , real           :: Bool       -- ^ supports real number arithmetic
  , fullcheck      :: Bool       -- ^ check all binders (overrides diffcheck)
  , saveQuery      :: Bool       -- ^ save fixpoint query
  , binders        :: [String]   -- ^ set of binders to check
  , noCheckUnknown :: Bool       -- ^ whether to complain about specifications for unexported and unused values
  , notermination  :: Bool       -- ^ disable termination check
  , autoproofs     :: Bool       -- ^ automatically construct proofs from axioms
  , nowarnings     :: Bool       -- ^ disable warnings output (only show errors)
  , trustinternals :: Bool       -- ^ type all internal variables with true
  , nocaseexpand   :: Bool       -- ^ disable case expand
  , strata         :: Bool       -- ^ enable strata analysis
  , notruetypes    :: Bool       -- ^ disable truing top level types
  , totality       :: Bool       -- ^ check totality in definitions
  , noPrune        :: Bool       -- ^ disable prunning unsorted Refinements
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
  , eliminate      :: Bool
  , port           :: Int        -- ^ port at which lhi should listen
  , exactDC        :: Bool       -- ^ Automatically generate singleton types for data constructors
  } deriving (Generic, Data, Typeable, Show, Eq)

instance Serialize SMTSolver
instance Serialize Config
