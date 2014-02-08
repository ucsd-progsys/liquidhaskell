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

module Language.Fixpoint.SmtLib2 ( 

    -- * Commands
      Command  (..)
    
    -- * Responses 
    , Response (..)
   
    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * Creating SMTLIB2 Process
    , makeContext 

    -- * Execute Queries
    , command
    ) where

import Language.Fixpoint.Config (SMTSolver (..))
import Language.Fixpoint.Files
import Language.Fixpoint.Types

import Data.Text.Format 
import Data.Text.Lazy     as T 
import Data.Text.Lazy.IO  as TIO 
import System.Process
import System.IO            (openFile, IOMode (..), Handle, hFlush)
import Control.Applicative  ((<$>))

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
-- commands :: Context -> [Command] -> IO [Response] 
-- -----------------------------------------------------------------------
-- commands = mapM . command 

--------------------------------------------------------------------------
command              :: Context -> Command -> IO Response 
--------------------------------------------------------------------------
command me cmd       = say me cmd >> hear me cmd
  where 
    say me           = smtWrite me . smt2
    hear me CheckSat = smtRead me
    hear me _        = return Ok



smtWrite         :: Context -> Raw -> IO ()
smtWrite me s    = smtWriteRaw me (T.append s "\n") 

smtRead          :: Context -> IO Response 
smtRead me       = do s <- smtReadRaw me
                      TIO.putStrLn $ format "SMT Says: {}" (Only s)
                      rs s 
  where
    rs "success" = smtRead me 
    rs "sat"     = return Sat
    rs "unsat"   = return Unsat
    rs "unknown" = return Unknown
    rs s         = return (Error s)

smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me s = hPutStrNow (cOut me) s >>  hPutStrNow (cLog me) s 

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = TIO.hGetLine (cIn me)

hPutStrNow h s   = TIO.hPutStr h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: SMTSolver -> IO Context 
--------------------------------------------------------------------------
makeContext s 
  = do me <- makeProcess s
       mapM_ (smtWrite me) $ smtPreamble s
       return me

makeProcess s 
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd s
       hLog                <- openFile smtFile WriteMode
       return $ Ctx pid hIn hOut hLog

{- "z3 -smt2 -in"                   -} 
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -} 
{- "z3 -smtc -in MBQI=false"        -} 

smtCmd Z3      = "z3 -smt2 -in MODEL=true MODEL.PARTIAL=true smt.mbqi=false auto-config=false"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

smtPreamble Z3 = z3Preamble
smtPreamble _  = smtlibPreamble

smtFile :: FilePath
smtFile = extFileName Smt2 "out" 

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtDecl me x ts t = interact' me (Declare x ts t)
smtPush me        = interact' me (Push)
smtPop me         = interact' me (Pop) 
smtAssert me p    = interact' me (Assert p)
smtDistinct me az = interact' me (Distinct az)
smtCheckUnsat me  = respSat <$> command me CheckSat

respSat Unsat     = True
respSat Sat       = False
respSat Unknown   = False
respSat r         = error "crash: SMTLIB2 respSat" 

interact' me cmd  = command me cmd >> return ()


--------------------------------------------------------------------------
-- | Set Theory ----------------------------------------------------------
--------------------------------------------------------------------------

elt, set :: Raw
elt = "Elt"
set = "Set"

emp, add, cup, cap, mem, dif, sub, com :: Raw
emp = "smt_set_emp"
add = "smt_set_add"
cup = "smt_set_cup"
cap = "smt_set_cap"
mem = "smt_set_mem"
dif = "smt_set_dif"
sub = "smt_set_sub"
com = "smt_set_com"

z3Preamble 
  = [ format "(define-sort {} () Int)"
        (Only elt)
    , format "(define-sort {} () (Array {} Bool))" 
        (set, elt)
    , format "(define-fun {} () {} ((as const {}) false))" 
        (emp, set, set) 
    , format "(define-fun {} ((x {}) (s {})) Bool (select s x))"
        (mem, elt, set)
    , format "(define-fun {} ((s {}) (x {})) {} (store s x true))"
        (add, set, elt, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map or) s1 s2))"
        (cup, set, set, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ((_ map and) s1 s2))"
        (cap, set, set, set)
    , format "(define-fun {} ((s {})) {} ((_ map not) s))"
        (com, set, set)
    , format "(define-fun {} ((s1 {}) (s2 {})) {} ({} s1 ({} s2)))"
        (dif, set, set, set, cap, com)
    , format "(define-fun {} ((s1 {}) (s2 {})) Bool (= {} ({} s1 s2)))"
        (sub, set, set, emp, dif) 
    ] 
 
smtlibPreamble
  = [        "(set-logic QF_UFLIA)"          
    , format "(define-sort {} () Int)"       (Only elt)
    , format "(define-sort {} () Int)"       (Only set) 
    , format "(declare-fun {} () {})"        (emp, set)
    , format "(declare-fun {} ({} {}) {})"   (add, set, elt, set)
    , format "(declare-fun {} ({} {}) {})"   (cup, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (cap, set, set, set)
    , format "(declare-fun {} ({} {}) {})"   (dif, set, set, set)
    , format "(declare-fun {} ({} {}) Bool)" (sub, set, set) 
    , format "(declare-fun {} ({} {}) Bool)" (mem, elt, set) 
    ] 

mkSetSort _ _  = set
mkEmptySet _ _ = emp
mkSetAdd _ s x = format "({} {} {})" (add, s, x) 
mkSetMem _ x s = format "({} {} {})" (mem, x, s) 
mkSetCup _ s t = format "({} {} {})" (cup, s, t)
mkSetCap _ s t = format "({} {} {})" (cap, s, t)
mkSetDif _ s t = format "({} {} {})" (dif, s, t)
mkSetSub _ s t = format "({} {} {})" (sub, s, t)

-----------------------------------------------------------------------
-- | AST Conversion ---------------------------------------------------
-----------------------------------------------------------------------

-- | Types that can be serialized
class SMTLIB2 a where
  smt2 :: a -> Raw

instance SMTLIB2 Sort where
  smt2 _ = "Int" 

instance SMTLIB2 Symbol where
  smt2 (S s) = T.pack s

instance SMTLIB2 SymConst where
  smt2 _ = error "TODO: SMTLIB2 SymConst"

instance SMTLIB2 Constant where
  smt2 (I n) = format "{}" (Only n)

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 Bop where
  smt2 Plus  = "+"
  smt2 Minus = "-"
  smt2 Times = "*"
  smt2 Div   = "/"
  smt2 Mod   = "mod"

instance SMTLIB2 Brel where
  smt2 Eq    = "="
  smt2 Ueq   = "="
  smt2 Gt    = ">"
  smt2 Ge    = ">="
  smt2 Lt    = "<" 
  smt2 Le    = "<="
  smt2 _     = error "SMTLIB2 Brel"

instance SMTLIB2 Expr where
  smt2 (ESym z)         = smt2 z
  smt2 (ECon c)         = smt2 c
  smt2 (EVar x)         = smt2 x
  smt2 (ELit x _)       = smt2 x
  smt2 (EApp f [])      = smt2 f
  smt2 (EApp f es)      = format "({} {})"        (smt2 f, smt2s es) 
  smt2 (EBin o e1 e2)   = format "({} {} {})"     (smt2 o, smt2 e1, smt2 e2)  
  smt2 (EIte e1 e2 e3)  = format "(ite {} {} {})" (smt2 e1, smt2 e2, smt2 e3)
  smt2 _                = error "TODO: SMTLIB2 Expr" 

instance SMTLIB2 Pred where
  smt2 (PTrue)          = "true"
  smt2 (PFalse)         = "false"
  smt2 (PAnd ps)        = format "(and {})"    (Only $ smt2s ps) 
  smt2 (POr ps)         = format "(or  {})"    (Only $ smt2s ps)
  smt2 (PNot p)         = format "(not {})"    (Only $ smt2 p)
  smt2 (PImp p q)       = format "(=> {} {})"  (smt2 p, smt2 q)
  smt2 (PIff p q)       = format "(=  {} {})"  (smt2 p, smt2 q)
  smt2 (PBexp e)        = smt2 e 
  smt2 (PAtom r e1 e2)  = mkRel r e1 e2 
  smt2 _                = error "smtlib2 Pred"


mkRel Ne  e1 e2         = mkNe e1 e2
mkRel Une e1 e2         = mkNe e1 e2
mkRel r   e1 e2         = format "({} {} {})"      (smt2 r, smt2 e1, smt2 e2)
mkNe  e1 e2             = format "(not (= {} {}))" (smt2 e1, smt2 e2)

instance SMTLIB2 Command where
  smt2 (Declare x ts t) = format "(declare-fun {} ({}) {})"  (smt2 x, smt2s ts, smt2 t)
  smt2 (Assert p)       = format "(assert {})"               (Only $ smt2 p)
  smt2 (Distinct az)    = format "(assert (distinct {}))"    (Only $ smt2s az)
  smt2 (Push)           = "(push 1)"
  smt2 (Pop)            = "(pop 1)"
  smt2 (CheckSat)       = "(check-sat)"

smt2s = T.intercalate " " . fmap smt2

{- 
(declare-fun x () Int) 
(declare-fun y () Int) 
(assert (<= 0 x)) 
(assert (< x y)) 
(push 1) 
(assert (not (<= 0 y))) 
(check-sat) 
(pop 1) 
(push 1) 
(assert (<= 0 y)) 
(check-sat) 
(pop 1)
-}
