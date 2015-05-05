{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}


module Language.Fixpoint.Config (
    Config  (..)
  , getOpts
  , Command (..)
  , SMTSolver (..)
  , GenQualifierSort (..)
  , UeqAllSorts (..)
  , withTarget
  , withUEqAllSorts
) where

import           System.Console.CmdArgs
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Data.Generics                  (Data)
import           Data.Typeable                  (Typeable)
import           Language.Fixpoint.Files
import           System.Console.CmdArgs.Default
import           System.FilePath


class Command a  where
  command :: a -> String

------------------------------------------------------------------------
-- Configuration Options -----------------------------------------------
------------------------------------------------------------------------

withTarget        :: Config -> FilePath -> Config
withTarget cfg fq = cfg { inFile = fq } { outFile = fq `withExt` Out }

data Config
  = Config {
      inFile      :: FilePath         -- ^ target fq-file
    , outFile     :: FilePath         -- ^ output file
    , srcFile     :: FilePath         -- ^ src file (*.hs, *.ts, *.c)
    , solver      :: SMTSolver        -- ^ which SMT solver to use
    , genSorts    :: GenQualifierSort -- ^ generalize qualifier sorts
    , ueqAllSorts :: UeqAllSorts      -- ^ use UEq on all sorts
    , native      :: Bool             -- ^ use haskell solver
    , real        :: Bool             -- ^ interpret div and mul in SMT
    , eliminate   :: Bool             -- ^ eliminate non-cut KVars
    } deriving (Eq,Data,Typeable,Show)

instance Default Config where
  def = Config "" def def def def def def def def
  
instance Command Config where
  command c =  command (genSorts c)
            ++ command (ueqAllSorts c)
            ++ command (solver c)
            ++ " -out "
            ++ (outFile c) ++ " " ++ (inFile c)

---------------------------------------------------------------------------------------
-- newtype OFilePath = O FilePath
--     deriving (Eq, Data,Typeable,Show)
--
-- instance Default OFilePath where
--   def = O "out"
--
-- instance Command OFilePath where
--   command (O s) = " -out " ++ s

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

withUEqAllSorts c b = c { ueqAllSorts = UAS b }

---------------------------------------------------------------------------------------

data SMTSolver = Z3 | Cvc4 | Mathsat | Z3mem
                 deriving (Eq,Data,Typeable)

instance Command SMTSolver where
  command s = " -smtsolver " ++ show s

instance Default SMTSolver where
  def = Z3

instance Show SMTSolver where
  show Z3      = "z3"
  show Cvc4    = "cvc4"
  show Mathsat = "mathsat"
  show Z3mem   = "z3mem"

smtSolver "z3"      = Z3
smtSolver "cvc4"    = Cvc4
smtSolver "mathsat" = Mathsat
smtSolver "z3mem"   = Z3mem
smtSolver other     = error $ "ERROR: unsupported SMT Solver = " ++ other

-- defaultSolver       :: Maybe SMTSolver -> SMTSolver
-- defaultSolver       = fromMaybe Z3


config = Config {
    inFile      = def   &= typ "TARGET"       &= args    &= typFile
  , outFile     = "out" &= help "Output file"
  , srcFile     = def   &= help "Source File from which FQ is generated"
  , solver      = def   &= help "Name of SMT Solver"
  , genSorts    = def   &= help "Generalize qualifier sorts"
  , ueqAllSorts = def   &= help "use UEq on all sorts"
  , native      = False &= help "(alpha) Haskell Solver"
  , real        = False &= help "(alpha) Theory of real numbers"
  , eliminate   = False &= help "(alpha) Eliminate non-cut KVars"
  }
  &= verbosity
  &= program "fixpoint"
  &= help    "Predicate Abstraction Based Horn-Clause Solver"
  &= summary "fixpoint Copyright 2009-13 Regents of the University of California."
  &= details [ "Predicate Abstraction Based Horn-Clause Solver"
             , ""
             , "To check a file foo.fq type:"
             , "  fixpoint foo.fq"
             ]

getOpts :: IO Config
getOpts = do md <- cmdArgs config
             putStrLn $ banner md
             return md

banner args =  "Liquid-Fixpoint Copyright 2009-13 Regents of the University of California.\n"
            ++ "All Rights Reserved.\n"

