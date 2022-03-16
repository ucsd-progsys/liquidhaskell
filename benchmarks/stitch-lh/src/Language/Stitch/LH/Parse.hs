{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--no-termination" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Parse
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Parses tokens into the un-type-checked AST. "Parsing", in stitch,
-- also includes name resolution. This all might
-- conceivably be done in a later pass, but there doesn't seem to be
-- an incentive to do so.
--
----------------------------------------------------------------------------

-- | Using an export list causes LH to crash with a stack overflow
module Language.Stitch.LH.Parse {- (
  parseStmtsM, parseStmts,
  parseStmtM, parseExpM,
  parseStmt, parseExp
  ) -} where

import Language.Stitch.LH.Unchecked
import Language.Stitch.LH.Statement
import Language.Stitch.LH.Token
import Language.Stitch.LH.Op
import Language.Stitch.LH.Type
import Language.Stitch.LH.Monad
import Language.Stitch.LH.Util


import Text.Parsec.Prim as Parsec hiding ( parse, (<|>) )
import Text.Parsec.Pos
import Text.Parsec.Combinator

import Text.PrettyPrint.ANSI.Leijen hiding ( (<$>) )

import qualified Data.List as List

import Control.Applicative
import Control.Arrow as Arrow ( left )
import Control.Monad.Identity
import Data.List (elemIndex)


-----------------------
-- Exports

-- | Parse a sequence of semicolon-separated statements, aborting with
-- an error upon failure
parseStmtsM :: [LToken] -> StitchE [Statement]
parseStmtsM = eitherToStitchE . parseStmts

-- | Parse a sequence of semicolon-separated statements
parseStmts :: [LToken] -> Either String [Statement]
parseStmts = parse stmts

-- | Parse a 'Statement', aborting with an error upon failure
parseStmtM :: [LToken] -> StitchE Statement
parseStmtM = eitherToStitchE . parseStmt

-- | Parse a 'Statement'
parseStmt :: [LToken] -> Either String Statement
parseStmt = parse stmt

-- | Parse a 'UExp', aborting with an error upon failure
{-@ parseExpM :: [LToken] -> StitchE ClosedUExp @-}
parseExpM :: [LToken] -> StitchE UExp
parseExpM = eitherToStitchE . parseExp

-- | Parse a 'UExp'
{-@ parseExp :: [LToken] -> Either String ClosedUExp @-}
parseExp :: [LToken] -> Either String UExp
parseExp = parse (expr [])

parse :: Parser a -> [LToken] -> Either String a
parse p toks = Arrow.left show $ runParser (p <* eof) () "" toks

----------------------
-- Plumbing

-- CHALLENGE: Explore using
--
-- > type Parser a = ParsecT [LToken] () (Reader [String]) a
--
-- instead of using CtxParser

type Parser a = Parsec [LToken] () a

-- | A parser usable in a context with the bound variables in the
-- argument list. Searching a bound name in the list gives you the
-- correct deBruijn index
type CtxParser a = [String] -> Parsec [LToken] () a

-- | Parse the given nullary token
tok :: Token -> Parser ()
tok t = tokenPrim (render . pretty) next_pos (guard . (t ==) . unLoc)

-- | Parse the given unary token
tok' :: (Token -> Maybe thing) -> Parser thing
tok' matcher = tokenPrim (render . pretty) next_pos (matcher . unLoc)

tokUnName :: Parser String
tokUnName = tok' unName

-- | Parse one of a set of 'ArithOp's
arith_op :: [ArithOp] -> Parser ArithOp
arith_op ops = tokenPrim (render . pretty) next_pos
                         (\case L _ (ArithOp op) | op `elem` ops -> Just op
                                _                                -> Nothing)

next_pos :: SourcePos  -- ^ position of the current token
         -> LToken     -- ^ current token
         -> [LToken]   -- ^ remaining tokens
         -> SourcePos  -- ^ location of the next token
next_pos pos _ []            = pos
next_pos _   _ (L pos _ : _) = pos

--------------
-- Real work

-- stmts :: Parser Zero [Statement]
stmts :: Parser [Statement]
stmts = stmt `sepEndBy` tok Semi

-- stmt :: Parser Zero Statement
-- XXX: LH crashes on stmt with: Unbound symbol lq_tmp$x##14994
stmt :: Parser Statement
-- XXX: Using $ for the argument of try crashes LH.
stmt = choice [ try (NewGlobal <$> tok' unName <* tok Assign <*> expr [])
              , BareExp <$> expr [] ]

{-@ expr :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
expr :: CtxParser UExp
expr ctx =
  choice [ lam ctx
         , cond ctx
         , let_exp ctx
         , int_exp ctx `chainl1` bool_op UArith ]

{-@ int_exp :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
int_exp :: CtxParser UExp
int_exp ctx = term ctx `chainl1` add_op UArith

{-@ term :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
term :: CtxParser UExp
term ctx = apps ctx `chainl1` mul_op UArith

{-@ apps :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
apps :: CtxParser UExp
apps ctx = choice [ UFix <$ tok FixTok <*> expr ctx
                  , List.foldl1 UApp <$> some (factor ctx) ]

{-@ factor :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
factor :: CtxParser UExp
factor ctx = choice [ between (tok LParen) (tok RParen) (expr ctx)
                    , UIntE <$> tok' unInt
                    , UBoolE <$> tok' unBool
                    , var ctx ]

{-@ lam :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
lam :: CtxParser UExp
-- XXX: Using do notation causes LH to fail with: Unbound symbol VV##5088
lam ctx =
  tok Lambda >>
  tok' unName >>= \bound_var ->
  tok Colon >>
  ty >>= \typ ->
  tok Dot >>
  expr (bound_var : ctx) >>= \e ->
  return (ULam typ e)

{-@ cond :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
cond :: CtxParser UExp
cond ctx = UCond <$ tok If <*> expr ctx <* tok Then <*> expr ctx <* tok Else <*> expr ctx

{-@ let_exp :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
let_exp :: CtxParser UExp
-- XXX: Using do notation causes LH to fail with: Unbound symbol VV##5088
let_exp ctx =
  tok LetTok >>
  tok' unName >>= \bound_var ->
  tok Assign >>
  expr ctx >>= \rhs ->
  tok InTok >>
  expr (bound_var : ctx) >>= \body ->
  return (ULet rhs body)

{-@ assume elemIndex :: Eq a => a -> xs : [a] -> Maybe { n:Nat | n < len xs } @-}

{-@ var :: ctx : [String] -> Parser {e : UExp | numFreeVars e <= len ctx } @-}
var :: CtxParser UExp
var ctx = do
  n <- tok' unName
  case elemIndex n ctx of
    Nothing -> return (UGlobal n)
    Just i  -> return (UVar i)

bool_op, add_op, mul_op :: (a -> ArithOp -> a -> a) -> Parser (a -> a -> a)
bool_op f = mk_op f <$> arith_op [Less, LessE, Greater, GreaterE, Equals]
add_op f = mk_op f <$> arith_op [Plus, Minus]
mul_op f = mk_op f <$> arith_op [Times, Divide, Mod]

mk_op :: (a -> ArithOp -> a -> a) -> ArithOp -> a -> a -> a
mk_op f = \op e1 e2 -> f e1 op e2

----------------------------------------
-- Types

ty :: Parser Ty
ty = chainr1 arg_ty (arrX <$ tok ArrowTok)
  where
    arrX :: Ty -> Ty -> Ty
    arrX arg res = TFun arg res

arg_ty :: Parser Ty
arg_ty = choice [ between (tok LParen) (tok RParen) ty
                , tycon ]

tycon :: Parser Ty
tycon = do
  n <- tok' unName
  case n of
    "Int"  -> return TInt
    "Bool" -> return TBool
    _      -> unexpected $ render $
              text "type name" <+> squotes (text n)
