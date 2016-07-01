{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric             #-}

module Language.Fixpoint.Types.Config (
    Config  (..)
  , defConfig
  , getOpts
  , Command (..)
  , SMTSolver (..)
  , GenQualifierSort (..)
  , UeqAllSorts (..)
  , defaultMinPartSize
  , defaultMaxPartSize
  , multicore
  , queryFile
) where

import Data.Maybe   (fromMaybe)
import Data.List    (find)
import GHC.Generics
import System.Console.CmdArgs
import Language.Fixpoint.Utils.Files

class Command a  where
  command :: a -> String

------------------------------------------------------------------------
-- Configuration Options -----------------------------------------------
------------------------------------------------------------------------

defaultMinPartSize :: Int
defaultMinPartSize = 500

defaultMaxPartSize :: Int
defaultMaxPartSize = 700

data Config
  = Config {
      inFile      :: FilePath            -- ^ target fq-file
    , srcFile     :: FilePath            -- ^ src file (*.hs, *.ts, *.c)
    , cores       :: Maybe Int           -- ^ number of cores used to solve constraints
    , minPartSize :: Int                 -- ^ Minimum size of a partition
    , maxPartSize :: Int                 -- ^ Maximum size of a partition. Overrides minPartSize
    , solver      :: SMTSolver           -- ^ which SMT solver to use
    , genSorts    :: GenQualifierSort    -- ^ generalize qualifier sorts
    , ueqAllSorts :: UeqAllSorts         -- ^ use UEq on all sorts
    , linear      :: Bool                -- ^ not interpret div and mul in SMT
    , allowHO     :: Bool                -- ^ allow higher order binders in the logic environment
    , allowHOqs   :: Bool                -- ^ allow higher order qualifiers
    , newcheck    :: Bool                -- ^ new fixpoint sort check
    , eliminate   :: Bool                -- ^ eliminate non-cut KVars
    , oldElim     :: Bool                -- ^ use old eliminate algorithm (deprecate)
    , elimBound   :: Maybe Int           -- ^ maximum length of KVar chain to eliminate
    , elimStats   :: Bool                -- ^ print eliminate stats
    , solverStats :: Bool                -- ^ print solver stats
    , metadata    :: Bool                -- ^ print meta-data associated with constraints
    , stats       :: Bool                -- ^ compute constraint statistics
    , parts       :: Bool                -- ^ partition FInfo into separate fq files
    , save        :: Bool                -- ^ save FInfo as .bfq and .fq file
    , minimize    :: Bool                -- ^ min .fq by delta debug (unsat with min constraints)
    , minimizeQs  :: Bool                -- ^ min .fq by delta debug (sat with min qualifiers)
    -- , nontriv     :: Bool             -- ^ simplify using non-trivial sorts
    , gradual     :: Bool                -- ^ solve "gradual" constraints
    , extensionality :: Bool             -- ^ allow function extensionality
    , alphaEquivalence :: Bool           -- ^ allow lambda alpha equivalence axioms
    , betaEquivalence  :: Bool           -- ^ allow lambda beta equivalence axioms
    , normalForm  :: Bool                -- ^ allow lambda normal-form equivalence axioms
    , autoKuts    :: Bool                -- ^ ignore given kut variables
    , pack        :: Bool                -- ^ Use pack annotations
    , nonLinCuts  :: Bool                -- ^ Treat non-linear vars as cuts
    } deriving (Eq,Data,Typeable,Show)


instance Default Config where
  def = Config { inFile      = ""
               , srcFile     = def
               , cores       = def
               , minPartSize = defaultMinPartSize
               , maxPartSize = defaultMaxPartSize
               , solver      = def
               , genSorts    = def
               , ueqAllSorts = def
               , linear      = def
               , allowHO     = False
               , allowHOqs   = False
               , newcheck    = False
               , eliminate   = False
               , oldElim     = True -- False
               , elimBound   = Nothing
               , elimStats   = def
               , solverStats = False
               , metadata    = def
               , stats       = def
               , parts       = def
               , save        = def
               , minimize    = def
               , minimizeQs  = def
               , gradual     = False
               , extensionality = False
               , alphaEquivalence = False
               , betaEquivalence  = False
               , normalForm     = False 
               , autoKuts       = False
               , pack           = False
               , nonLinCuts     = False
               }
defConfig :: Config
defConfig = def

---------------------------------------------------------------------------------------
newtype GenQualifierSort = GQS Bool
    deriving (Eq, Data,Typeable,Show)

instance Default GenQualifierSort where
  def = GQS False

instance Command GenQualifierSort where
  command (GQS True)  = ""
  command (GQS False) = "-no-gen-qual-sorts"

newtype UeqAllSorts = UAS Bool
    deriving (Eq, Data,Typeable,Show)

instance Default UeqAllSorts where
  def = UAS False

instance Command UeqAllSorts where
  command (UAS True)  = " -ueq-all-sorts "
  command (UAS False) = ""

-- instance Command Cores where
--   command (C n) = " --cores=" ++ show n


---------------------------------------------------------------------------------------

data SMTSolver = Z3 | Cvc4 | Mathsat
                 deriving (Eq, Data, Typeable, Generic)

instance Command SMTSolver where
  command s = " -smtsolver " ++ show s

instance Default SMTSolver where
  def = Z3

instance Show SMTSolver where
  show Z3      = "z3"
  show Cvc4    = "cvc4"
  show Mathsat = "mathsat"

---------------------------------------------------------------------------------------

config :: Config
config = Config {
    inFile      = def     &= typ "TARGET"       &= args    &= typFile
  , srcFile     = def     &= help "Source File from which FQ is generated"
  , solver      = def     &= help "Name of SMT Solver"
  , genSorts    = def     &= help "Generalize qualifier sorts"
  , ueqAllSorts = def     &= help "Use UEq on all sorts"
  , newcheck    = False   &= help "(alpha) New liquid-fixpoint sort checking "
  , linear      = False   &= help "Use uninterpreted integer multiplication and division"
  , allowHO     = False   &= help "Allow higher order binders into fixpoint environment"
  , allowHOqs   = False   &= help "Allow higher order qualifiers"
  , eliminate   = False   &= help "Eliminate non-cut KVars"
  , oldElim     = True    &= help "(default) Use old eliminate algorithm"
  , elimBound   = Nothing &= name "elimBound"
                          &= help "(alpha) Maximum eliminate-chain depth"
  , elimStats   = False   &= help "(alpha) Print eliminate stats"
  , solverStats = False   &= help "Print solver stats"
  , save        = False   &= help "Save Query as .fq and .bfq files"
  , metadata    = False   &= help "Print meta-data associated with constraints"
  , stats       = False   &= help "Compute constraint statistics"
  , parts       = False   &= help "Partition constraints into indepdendent .fq files"
  , cores       = def     &= help "(numeric) Number of threads to use"
  , minPartSize = defaultMinPartSize &= help "(numeric) Minimum partition size when solving in parallel"
  , maxPartSize = defaultMaxPartSize &= help "(numeric) Maximum partiton size when solving in parallel."
  , minimize    = False &= help "Delta debug to minimize fq file (unsat with min constraints)"
  , minimizeQs  = False &= help "Delta debug to minimize fq file (sat with min qualifiers)"
  , gradual     = False &= help "Solve gradual-refinement typing constraints"
  , extensionality = False &= help "Allow function extensionality axioms"
  , alphaEquivalence = False &= help "Allow lambda alpha equivalence axioms"
  , betaEquivalence = False &= help "Allow lambda alpha equivalence axioms"
  , normalForm     = False  &= help "Allow lambda normal-form equivalence axioms"
  , autoKuts       = False &= help "Ignore given Kut vars, compute from scratch"
  , pack           = False &= help "Use pack annotations"
  , nonLinCuts     = False &= help "Treat non-linear kvars as cuts"
  }
  &= verbosity
  &= program "fixpoint"
  &= help    "Predicate Abstraction Based Horn-Clause Solver"
  &= summary "fixpoint Copyright 2009-15 Regents of the University of California."
  &= details [ "Predicate Abstraction Based Horn-Clause Solver"
             , ""
             , "To check a file foo.fq type:"
             , "  fixpoint foo.fq"
             ]

getOpts :: IO Config
getOpts = do md <- cmdArgs config
             putStrLn banner
             return md

banner :: String
banner =  "\n\nLiquid-Fixpoint Copyright 2013-15 Regents of the University of California.\n"
       ++ "All Rights Reserved.\n"

multicore :: Config -> Bool
multicore cfg = cores cfg /= Just 1

queryFile :: Ext -> Config -> FilePath
queryFile e cfg = extFileName e f
  where
    f           = fromMaybe "out" $ find (not . null) [srcFile cfg, inFile cfg]
