{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}

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

    -- * Creating and killing SMTLIB2 Process
    , Context (..)
    , makeContext
    , cleanupContext

    -- * Execute Queries
    , command
    , smtWrite
    ) where

import Language.Fixpoint.Config (SMTSolver (..))
import Language.Fixpoint.Files
import Language.Fixpoint.Types

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.List as L
import Data.Monoid
import Data.Text.Format
import qualified Data.Text          as ST
import qualified Data.Text.Lazy     as T
import qualified Data.Text.Lazy.IO  as TIO
import System.Exit
import System.Process
import System.IO            (openFile, IOMode (..), Handle, hFlush, hClose)
import Control.Applicative  ((<$>), (<|>), (*>), (<*))

import Text.Parsec.Text.Lazy ()
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim (ParsecT, runPT, getState, setInput, try)

{- Usage:
runFile f
  = readFile f >>= runString

runString str
  = runCommands $ rr str

runCommands cmds 
  = do me   <- makeContext Z3
       mapM_ (T.putStrLn . smt2) cmds
       zs   <- mapM (command me) cmds
       return zs
-}

--------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------
--------------------------------------------------------------------------

type Raw          = T.Text

-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | Declare   Symbol [Sort] Sort
                  | Define    Sort
                  | Assert    (Maybe Int) Pred
                  | Distinct  [Expr] -- {v:[Expr] | (len v) >= 2}
                  | GetValue  [Symbol]
                  deriving (Eq, Show)

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, Raw)]
                  | Error Raw
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context      = Ctx { pId  :: ProcessHandle
                        , cIn  :: Handle
                        , cOut :: Handle
                        , cLog :: Handle
                        , verbose :: Bool
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
    hear me (GetValue _) = smtRead me
    hear me _        = return Ok



smtWrite         :: Context -> Raw -> IO ()
smtWrite me s    = smtWriteRaw me (T.append s "\n")

smtRead :: Context -> IO Response
smtRead me
  = do ln <- smtReadRaw me
       res <- runPT responseP me "" ln
       case res of
         Left e  -> error $ show e
         Right r -> do
           hPutStrNow (cLog me) $ format "; SMT Says: {}\n" (Only $ show r)
           when (verbose me) $
             TIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
           return r

type Parser = ParsecT T.Text Context IO

responseP :: Parser Response
responseP =  try (string "(error")  *> errorP
         <|>      char   '('        *> valuesP
         <|> try (string "success") *> responseP
         <|>      string "sat"      *> return Sat
         <|> try (string "unsat")   *> return Unsat
         <|>      string "unknown"  *> return Unknown

valuesP :: Parser Response
valuesP = Values <$> many1 (spaces *> valueP)

valueP :: Parser (Symbol, Raw)
valueP
  = do (x,v) <- parens $ do
         x <- symbol . ST.pack <$> many1 (alphaNum <|> oneOf "_.-#%")
         spaces
         v <-  parens (many1 (satisfy (/=')')) >>= \s -> return $ "("<>s<>")")
           <|> many1 alphaNum
         return (x,v)
       -- get next line
       try (char ')' >> return ()) <|> getNextLine
       return (x,T.pack v)

getNextLine
  = do ln <- liftIO . smtReadRaw =<< getState
       setInput ln

parens p = char '(' *> p <* char ')'

errorP = Error . T.pack <$> (spaces *> quotedP anyChar <* char ')')
  where
    quotedP p = do string "\""
                   manyTill p (try $ string "\"")


{-@ pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] @-}
pairs :: [a] -> [(a,a)]
pairs = go
  where
    go xs = case L.splitAt 2 xs of
              ([],b)        -> []
              ((x:y:[]),zs) -> (x,y) : pairs zs

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
       return $ Ctx pid hIn hOut hLog False

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext me@(Ctx {..})
  = do smtWrite me "(exit)"
       code <- waitForProcess pId
       hClose cIn
       hClose cOut
       hClose cLog
       return code

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

-- ERIC: Do we really need to set mbqi to false? It seems useful for generating test data
smtCmd Z3      = "z3 -smt2 -in MODEL=true MODEL.PARTIAL=true auto-config=false"
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
smtAssert me p    = interact' me (Assert Nothing p)
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
  smt2 FInt        = "Int"
  smt2 (FApp t []) | t == propFTyCon = "Bool"
  smt2 (FObj s)    = smt2 s
  smt2 (FFunc _ _) = error "smt2 FFunc"
  smt2 _           = "Int"

instance SMTLIB2 Symbol where
  smt2 s = T.fromStrict $ symbolText s

instance SMTLIB2 SymConst where
  smt2 (SL s) = T.fromStrict $ s

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
  smt2 (Declare x ts t)    = format "(declare-fun {} ({}) {})"  (smt2 x, smt2s ts, smt2 t)
  smt2 (Define t)          = format "(declare-sort {})"         (Only $ smt2 t)
  smt2 (Assert Nothing p)  = format "(assert {})"               (Only $ smt2 p)
  smt2 (Assert (Just i) p) = format "(assert (! {} :named p-{}))"  (smt2 p, i)
  smt2 (Distinct az)       = format "(assert (distinct {}))"    (Only $ smt2s az)
  smt2 (Push)              = "(push 1)"
  smt2 (Pop)               = "(pop 1)"
  smt2 (CheckSat)          = "(check-sat)"
  smt2 (GetValue xs)       = T.unwords $ ["(get-value ("] ++ map smt2 xs ++ ["))"]

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
