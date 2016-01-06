{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric             #-}

module Language.Fixpoint.Types.Config (
    Config  (..)
  , getOpts
  , Command (..)
  , SMTSolver (..)
  , GenQualifierSort (..)
  , UeqAllSorts (..)
  , withTarget
  , defaultMinPartSize
  , defaultMaxPartSize
  , multicore
) where

import GHC.Generics
import System.Console.CmdArgs
import Language.Fixpoint.Utils.Files
import Language.Fixpoint.Misc (errorstar)

class Command a  where
  command :: a -> String

------------------------------------------------------------------------
-- Configuration Options -----------------------------------------------
------------------------------------------------------------------------

withTarget        :: Config -> FilePath -> Config
withTarget cfg fq = cfg { inFile = fq } { outFile = fq `withExt` Out }

defaultMinPartSize :: Int
defaultMinPartSize = 500

defaultMaxPartSize :: Int
defaultMaxPartSize = 700

data Config
  = Config {
      inFile      :: FilePath            -- ^ target fq-file
    , outFile     :: FilePath            -- ^ output file
    , srcFile     :: FilePath            -- ^ src file (*.hs, *.ts, *.c)
    , cores       :: Maybe Int           -- ^ number of cores used to solve constraints
    , minPartSize :: Int                 -- ^ Minimum size of a partition
    , maxPartSize :: Int                 -- ^ Maximum size of a partition. Overrides minPartSize
    , solver      :: SMTSolver           -- ^ which SMT solver to use
    , genSorts    :: GenQualifierSort    -- ^ generalize qualifier sorts
    , ueqAllSorts :: UeqAllSorts         -- ^ use UEq on all sorts
    , real        :: Bool                -- ^ interpret div and mul in SMT
    , newcheck    :: Bool                -- ^ new fixpoint sort check
    , eliminate   :: Bool                -- ^ eliminate non-cut KVars
    , elimStats   :: Bool                -- ^ print eliminate stats
    , metadata    :: Bool                -- ^ print meta-data associated with constraints
    , stats       :: Bool                -- ^ compute constraint statistics
    , parts       :: Bool                -- ^ partition FInfo into separate fq files
    , save        :: Bool                -- ^ save FInfo as .bfq and .fq file
    -- , nontriv     :: Bool             -- ^ simplify using non-trivial sorts
    } deriving (Eq,Data,Typeable,Show)


instance Default Config where
  def = Config { inFile      = ""
               , outFile     = def
               , srcFile     = def
               , cores       = def
               , minPartSize = defaultMinPartSize
               , maxPartSize = defaultMaxPartSize
               , solver      = def
               , genSorts    = def
               , ueqAllSorts = def
               , real        = def
               , newcheck    = False
               , eliminate   = def
               , elimStats   = def
               , metadata    = def
               , stats       = def
               , parts       = def
               , save        = def
               }

instance Command Config where
  command c =  command (genSorts c)
            ++ command (ueqAllSorts c)
            ++ command (solver c)
            ++ " -out "
            ++ outFile c ++ " "
            ++ inFile c

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

data SMTSolver = Z3 | Cvc4 | Mathsat | Z3mem
                 deriving (Eq, Data, Typeable, Generic)

instance Command SMTSolver where
  command s = " -smtsolver " ++ show s

instance Default SMTSolver where
  def = Z3

instance Show SMTSolver where
  show Z3      = "z3"
  show Cvc4    = "cvc4"
  show Mathsat = "mathsat"
  show Z3mem   = "z3mem"

---------------------------------------------------------------------------------------

config :: Config
config = Config {
    inFile      = def   &= typ "TARGET"       &= args    &= typFile
  , outFile     = "out" &= help "Output file"
  , srcFile     = def   &= help "Source File from which FQ is generated"
  , solver      = def   &= help "Name of SMT Solver"
  , genSorts    = def   &= help "Generalize qualifier sorts"
  , ueqAllSorts = def   &= help "Use UEq on all sorts"
  , newcheck    = False &= help "(alpha) New liquid-fixpoint sort checking "
  , real        = False &= help "(alpha) Theory of real numbers"
  , eliminate   = False &= help "(alpha) Eliminate non-cut KVars"
  , elimStats   = False &= help "(alpha) Print eliminate stats"
  , save        = False &= help "Save Query as .fq and .bfq files"
  , metadata    = False &= help "Print meta-data associated with constraints"
  , stats       = False &= help "Compute constraint statistics"
  , parts       = False &= help "Partition constraints into indepdendent .fq files"
  , cores       = def   &= help "(numeric) Number of threads to use"
  , minPartSize = defaultMinPartSize &= help "(numeric) Minimum partition size when solving in parallel"
  , maxPartSize = defaultMaxPartSize &= help "(numeric) Maximum partiton size when solving in parallel."
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
