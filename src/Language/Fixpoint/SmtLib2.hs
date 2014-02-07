{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE OverloadedStrings	       #-}

-- | This module contains an SMTLIB2 interface for
--   1. checking the validity, and,
--   2. computing satisfying assignments 
--   for formulas.
--   By implementing a binary interface over the SMTLIB2 format defined at  
--   http://www.smt-lib.org/                                    
--   http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf

module Language.Fixpoint.SMTLIB2 where

import Language.Fixpoint.Files
import Language.Fixpoint.Types

import Data.Text.Format (format)
import Data.Text.Lazy as T 

import System.Process

--------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------
--------------------------------------------------------------------------

type Raw          = T.Text

-- | Commands issued to SMT engine
data Command      = Push 
                  | Pop 
              	  | CheckSat
                  | Declare   Symbol [Sort] Sort 
                  | Assert    Pred 
                  | Distinct  [Expr] -- {v:[Expr] | (len v) >= 2}
                  deriving (Eq, Show)

-- | Responses received from SMT engine
data Response     = Ok 
                  | Sat 
                  | Unsat 
                  | Unknown 
                  | Error Raw 
                  deriving (Eq, Show)

-- | Supported solvers 
data Solver       = Z3 
                  | Mathsat 
                  | Cvc4

-- | Information about the external SMT process 
data Context      = Ctx { pId  :: ProcessHandle
                        , cIn  :: Handle
                        , cOut :: Handle 
                        , cLog :: Handle
                        }

--------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
interact             :: Context -> Command -> IO Response 
--------------------------------------------------------------------------
interact me cmd      = say me cmd >> hear me cmd
  where 
    say me           = smtWrite me . smt2
    hear me CheckSat = smtRead me
    hear me _        = return Ok

smtWrite         :: Context -> Raw -> IO ()
smtWrite me s    = smtWriteRaw me (T.append s "\n") 

smtReadRaw       :: Context -> IO Response 
smtRead me       = smtReadRaw me >>= rs me
  where
    rs "success" = smtRead me 
    rs "sat"     = return Sat
    rs "unsat"   = return Unsat
    rs "unknown" = return Unknown
    rs s         = return (Error s)

smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me s = output_now (cLog me) s >> output_now (cOut me) s

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = hGetLine (cIn me)

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: Solver -> IO Context 
--------------------------------------------------------------------------
makeContext s 
  = do me <- makeProcess s
       mapM_ (smtWrite me) $ smtPreamble s
       return me

makeContext   :: Solver -> IO Context 
makeProcess s 
  = do (Just hOut, Just hIn, _ ,pid) <- createProcess smtProc s
       hLog                          <- openFile smtFile WriteMode
       return $ Ctx pid hIn hOut hLog

{- "z3 -smt2 -in"                   -} 
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -} 
{- "z3 -smtc -in MBQI=false"        -} 

smtProc s      = (proc cmd []) {std_out = CreatePipe } {std_in = CreatePipe }
  where
    cmd        = smtCmd s

smtCmd Z3      = "z3 -smt2 -in MODEL=true MODEL.PARTIAL=true smt.mbqi=false auto-config=false"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

smtPreamble Z3 = z3Preamble
smtPreamble _  = smtlibPreamble

smtFile :: FilePath
smtFile = extFileName Smt2 "out" 

-- let solver () =
--   match !Co.smt_solver with
--     | Some "z3"      -> Z3
--     | Some "mathsat" -> Mathsat
--     | Some "cvc4"    -> Cvc4
--     | Some str       -> assertf "ERROR: fixpoint does not yet support SMTSOLVER: %s" str
--     | None           -> assertf "ERROR: undefined solver for smtLIB2"


-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtDecl me x ts t = interact' me (Declare x ts t) 
smtPush me        = interact' me (Push)
smtPop me         = interact' me (Pop) 
smtAssert me p    = interact' me (Assert p)
smtDistinct me az = interact' me (Distinct az)
smtCheckUnsat me  = respSat <$> interact me CheckSat

respSat Unsat     = True
respSat Sat       = False
respSat Unknown   = False
respSat r         = throw $ "crash: SMTLIB2 respSat" 

interact' me cmd  = interact me cmd >> return ()


--------------------------------------------------------------------------
-- | AST Constructors ----------------------------------------------------
--------------------------------------------------------------------------



--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt = So "Elt"
set = So "Set"
emp = Sy "smt_set_emp"
add = Sy "smt_set_add"
cup = Sy "smt_set_cup"
cap = Sy "smt_set_cap"
mem = Sy "smt_set_mem"
dif = Sy "smt_set_dif"
sub = Sy "smt_set_sub"
com = Sy "smt_set_com"

z3Preamble 
  = [ spr "(define-sort {} () Int)"
        (Only elt)
    , spr "(define-sort {} () (Array {} Bool))" 
        (set, elt)
    , spr "(define-fun {} () {} ((as const {}) false))" 
        (emp, set, set) 
    , spr "(define-fun {} ((x {}) (s {})) Bool (select s x))"
        (mem, elt, set)
    , spr "(define-fun {} ((s {}) (x {})) {} (store s x true))"
        (add, set, elt, set)
    , spr "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map or) s1 s2))"
        (cup, set, set, set)
    , spr "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map and) s1 s2))"
        (cap, set, set, set)
    , spr "(define-fun {} ((s {})) {} ((_ map not) s))"
        (com, set, set)
    , spr "(define-fun {} ((s1 {}) (s2 {})) {} ({} s1 ({} s2)))"
        (dif, set, set, set, cap, com)
    , spr "(define-fun {} ((s1 {}) (s2 {})) Bool (= {} ({} s1 s2)))"
        (sub, set, set, emp, dif) 
    ] 
 
smtlibPreamble
  = [ spr "(set-logic QF_UFLIA)"
    , spr "(define-sort {} () Int)"       (Only elt)
    , spr "(define-sort {} () Int)"       (Only set) 
    , spr "(declare-fun {} () {})"        (emp, set)
    , spr "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , spr "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , spr "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , spr "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , spr "(declare-fun {} ({} {}) Bool)" (sub, set, set) 
    , spr "(declare-fun {} ({} {}) Bool)" (mem, elt, set) 
    ] 

mkSetSort _ _  = set
mkEmptySet _ _ = emp
mkSetAdd _ s x = spr "({} {} {})" (add, s, x) 
mkSetMem _ x s = spr "({} {} {})" (mem, x, s) 
mkSetCup _ s t = spr "({} {} {})" (cup, s, t)
mkSetCap _ s t = spr "({} {} {})" (cap, s, t)
mkSetDif _ s t = spr "({} {} {})" (dif, s, t)
mkSetSub _ s t = spr "({} {} {})" (sub, s, t)


-----------------------------------------------------------------------
-- | Conversion -------------------------------------------------------
-----------------------------------------------------------------------

spr = format

instance SMTLIB2 a => HEREHEREHERE 

-- | Types that can be serialized
class SMTLIB2 a where
  smt2 :: a -> Raw

instance SMTLIB2 Symbol where
  smt2 = undefined

instance Rawable Sort where
  smt2 = undefined

instance Rawable Expr where
  smt2 = undefined

instance Rawable Pred where
  smt2 = undefined

instance SMTLIB2 Command where
  smt2 (Declare x ts t) = spr "(declare-fun {} ({}) {})"  (x, smt2 ts, t)
  smt2 (Assert p)       = spr "(assert {})"               (Only $ smt2 p)
  smt2 (Distinct az)    = spr "(assert (distinct {}))"    (Only $ smt2 ts)
  smt2 (Push)           = "(push 1)"
  smt2 (Pop)            = "(pop 1)"
  smt2 (CheckSat)       = "(check-sat)"

instance SMTLIB2 a => SMTLIB2 [a] where
  smt2 = T.intercalate " " . map smt2
