{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}


module Language.Fixpoint.Config (
    Config  (..)
  , Command (..)
  , SMTSolver (..)
  , GenQualifierSort (..)
  , withTarget 
) where  
  
import Language.Fixpoint.Files
import System.FilePath       
import System.Console.CmdArgs.Default
import Data.Typeable        (Typeable)
import Data.Generics        (Data)


class Command a  where
  command :: a -> String

------------------------------------------------------------------------
-- Configuration Options -----------------------------------------------
------------------------------------------------------------------------

withTarget        :: Config -> FilePath -> Config 
withTarget cfg fq = cfg { inFile = fq } { outFile = fq `withExt` Out }

data Config 
  = Config { 
      inFile   :: FilePath         -- target fq-file 
    , outFile  :: FilePath         -- output file
    , solver   :: SMTSolver        -- which SMT solver to use 
    , genSorts :: GenQualifierSort -- generalize qualifier sorts
    , native   :: Bool             -- use haskell solver
    , real     :: Bool             -- use haskell solver
    } deriving (Eq,Data,Typeable,Show)

instance Default Config where
  def = Config "" def def def def def

instance Command Config where 
  command c =  command (genSorts c)    
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


