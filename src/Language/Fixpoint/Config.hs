{-# LANGUAGE DeriveDataTypeable        #-}
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
  , toCores
) where

import           System.Console.CmdArgs
import           Language.Fixpoint.Files


class Command a  where
  command :: a -> String

------------------------------------------------------------------------
-- Configuration Options -----------------------------------------------
------------------------------------------------------------------------

withTarget        :: Config -> FilePath -> Config
withTarget cfg fq = cfg { inFile = fq } { outFile = fq `withExt` Out }

data Cores = C Int
          deriving (Eq, Data, Show, Typeable) 

instance Num Cores where
  (C n1) + (C n2) = C (n1 + n2)
  (C n1) * (C n2) = C (n1 * n2)
  abs (C n)       = C $ abs n 
  signum (C n)    = C $ signum n 
  fromInteger     = C . fromInteger   
  negate (C n)    = C $ negate n

toCores = C 

data Config
  = Config {
      inFile      :: FilePath         -- ^ target fq-file
    , outFile     :: FilePath         -- ^ output file
    , srcFile     :: FilePath         -- ^ src file (*.hs, *.ts, *.c)
    , cores       :: Cores            -- ^ number of cores used to solve constraints
    , solver      :: SMTSolver        -- ^ which SMT solver to use
    , genSorts    :: GenQualifierSort -- ^ generalize qualifier sorts
    , ueqAllSorts :: UeqAllSorts      -- ^ use UEq on all sorts
    , native      :: Bool             -- ^ use haskell solver
    , real        :: Bool             -- ^ interpret div and mul in SMT
    , eliminate   :: Bool             -- ^ eliminate non-cut KVars
    , metadata    :: Bool             -- ^ print meta-data associated with constraints
    , stats       :: Bool             -- ^ compute constraint statistics
    , parts       :: Bool             -- ^ partition FInfo into separate fq files
    } deriving (Eq,Data,Typeable,Show)

instance Default Config where
  def = Config "" def def 1 def def def def def def def def def

instance Command Config where
  command c =  command (genSorts c)
            ++ command (ueqAllSorts c)
            ++ command (solver c)
            ++ command (cores c)
            ++ " -out "
            ++ outFile c ++ " " ++ inFile c

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

instance Command Cores where
  command (C n) = " --cores=" ++ show n  


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

config :: Config
config = Config {
    inFile      = def   &= typ "TARGET"       &= args    &= typFile
  , outFile     = "out" &= help "Output file"
  , srcFile     = def   &= help "Source File from which FQ is generated"
  , solver      = def   &= help "Name of SMT Solver"
  , genSorts    = def   &= help "Generalize qualifier sorts"
  , ueqAllSorts = def   &= help "Use UEq on all sorts"
  , native      = False &= help "(alpha) Haskell Solver"
  , real        = False &= help "(alpha) Theory of real numbers"
  , eliminate   = False &= help "(alpha) Eliminate non-cut KVars"
  , metadata    = False &= help "Print meta-data associated with constraints"
  , stats       = False &= help "Compute constraint statistics"
  , parts       = False &= help "Partition constraints into indepdendent .fq files"
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
banner =  "Liquid-Fixpoint Copyright 2009-13 Regents of the University of California.\n"
       ++ "All Rights Reserved.\n"
