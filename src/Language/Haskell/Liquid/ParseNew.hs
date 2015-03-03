{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Haskell.Liquid.ParseNew where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Int
import Data.Monoid

import Text.Parser.Char
import Text.Parser.Combinators
import Text.Parser.Expression
import Text.Parser.Token
import Text.Parser.Token.Style
import qualified Text.Trifecta as P
import qualified Text.Trifecta.Delta as P

import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types hiding (var)



data ParserState = PS { seed :: !Int, col :: !Int64 } deriving (Show)

initParserState :: ParserState
initParserState = PS 0 0

newtype Parser a = Parser { runParser :: StateT ParserState P.Parser a }
  deriving ( Functor, Applicative, Alternative, Monad, MonadPlus
           , MonadState ParserState
           , P.Parsing, P.CharParsing, P.DeltaParsing
           )

instance TokenParsing Parser where
  someSpace = buildSomeSpaceParser (skipSome space) haskellCommentStyle
  token p = notEndBlock *> p <* (someSpace <|> pure ())

notEndBlock :: Parser ()
notEndBlock = do
  col <- gets col
  c   <- P.column <$> P.position
  when (c < col) (fail "end of block")

pushIndent :: Parser ()
pushIndent = do
  c <- P.column <$> P.position
  modify $ \ s -> s { col = c }

hang :: Parser a -> (a -> Parser b) -> Parser b
hang p k = do
  col <- gets col
  c <- P.column <$> P.position
  a <- p
  modify $ \ s -> s { col = c + 1 }
  r <- k a
  modify $ \ s -> s { col = col }
  return r

indented :: Parser a -> Parser a
indented p = do
  col <- gets col
  c <- P.column <$> P.position
  modify $ \ s -> s { col = c }
  x <- p
  modify $ \ s -> s { col = col }
  return x

parseTest :: (MonadIO m, Show a) => Parser a -> String -> m ()
parseTest p s = P.parseTest (evalStateT (runParser p) initParserState) s

----------------------------------------------------------------------
-- Language Definition
----------------------------------------------------------------------

idStyle :: IdentifierStyle Parser
idStyle = haskellIdents

identifier :: Parser String
identifier = ident idStyle

reserved :: String -> Parser ()
reserved = reserve idStyle

reservedOp :: String -> Parser ()
reservedOp = reserve emptyOps


expr :: Parser F.Expr
expr =  buildExpressionParser bops compound
    <?> "expression"

compound :: Parser F.Expr
compound = ite <|> try app <|> term

term :: Parser F.Expr
term =  parens expr
    <|> var

ite :: Parser F.Expr
ite = do
  reserved "if"
  b <- expr
  reserved "then"
  t <- expr
  reserved "else"
  e <- expr
  return $ F.EIte F.PTrue t e

app :: Parser F.Expr
app = do
  f    <- identifier
  args <- many (notEndBlock *> term)
  return $ F.EApp (F.dummyLoc $ F.symbol f) args

var :: Parser F.Expr
var = F.EVar . F.symbol <$> identifier

bops = [ [ Prefix (reservedOp "-"   >> return F.ENeg)]
       , [ Infix  (reservedOp "*"   >> return (F.EBin F.Times)) AssocLeft
         , Infix  (reservedOp "/"   >> return (F.EBin F.Div  )) AssocLeft
         ]
       , [ Infix  (reservedOp "-"   >> return (F.EBin F.Minus)) AssocLeft
         , Infix  (reservedOp "+"   >> return (F.EBin F.Plus )) AssocLeft
         ]
       , [ Infix  (reserved  "mod"  >> return (F.EBin F.Mod  )) AssocLeft]
       ]
