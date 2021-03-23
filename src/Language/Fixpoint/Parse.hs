{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}

module Language.Fixpoint.Parse (

  -- * Top Level Class for Parseable Values
    Inputable (..)

  -- * Top Level Class for Parseable Values
  , Parser

  -- * Some Important keyword and parsers
  , reserved, reservedOp
  , locReserved
  , parens  , brackets, angles, braces
  , semi    , comma
  , colon   , dcolon
  , dot
  , pairP
  , stringLiteral
  , locStringLiteral

  -- * Parsing basic entities

  --   fTyConP  -- Type constructors
  , lowerIdP    -- Lower-case identifiers
  , upperIdP    -- Upper-case identifiers
  -- , infixIdP    -- String Haskell infix Id
  , symbolP     -- Arbitrary Symbols
  , locSymbolP
  , constantP   -- (Integer) Constants
  , natural     -- Non-negative integer
  , locNatural
  , bindP       -- Binder (lowerIdP <* colon)
  , sortP       -- Sort
  , mkQual      -- constructing qualifiers
  , infixSymbolP -- parse infix symbols
  , locInfixSymbolP

  -- * Parsing recursive entities
  , exprP       -- Expressions
  , predP       -- Refinement Predicates
  , funAppP     -- Function Applications
  , qualifierP  -- Qualifiers
  , refaP       -- Refa
  , refP        -- (Sorted) Refinements
  , refDefP     -- (Sorted) Refinements with default binder
  , refBindP    -- (Sorted) Refinements with configurable sub-parsers
  , bvSortP     -- Bit-Vector Sort
  , defineP     -- function definition equations (PLE)
  , matchP      -- measure definition equations (PLE)

  -- * Layout
  , indentedBlock
  , indentedLine
  , indentedOrExplicitBlock
  , explicitBlock
  , explicitCommaBlock
  , block
  , spaces
  , setLayout
  , popLayout

  -- * Raw identifiers
  , condIdR

  -- * Lexemes and lexemes with location
  , lexeme
  , located
  , locLexeme
  , locLowerIdP
  , locUpperIdP

  -- * Getting a Fresh Integer while parsing
  , freshIntP

  -- * Parsing Function
  , doParse'
  , parseTest'
  , parseFromFile
  , parseFromStdIn
  , remainderP

  -- * Utilities
  , isSmall
  , isNotReserved

  , initPState, PState (..)

  , LayoutStack(..)
  , Fixity(..), Assoc(..), addOperatorP

  -- * For testing
  , expr0P
  , dataFieldP
  , dataCtorP
  , dataDeclP

  ) where

import           Control.Monad.Combinators.Expr
import qualified Data.IntMap.Strict          as IM
import qualified Data.HashMap.Strict         as M
import qualified Data.HashSet                as S
import           Data.List                   (foldl')
import           Data.List.NonEmpty          (NonEmpty(..))
import qualified Data.Text                   as T
import qualified Data.Text.IO                as T
import           Data.Maybe                  (fromJust, fromMaybe)
import           Data.Void
import           Text.Megaparsec             hiding (State, ParseError)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer  as L
import           GHC.Generics                (Generic)

import qualified Data.Char                   as Char
import           Language.Fixpoint.Smt.Bitvector
import           Language.Fixpoint.Types.Errors
import qualified Language.Fixpoint.Misc      as Misc
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Types hiding    (mapSort)
import           Text.PrettyPrint.HughesPJ         (text, vcat, (<+>), Doc)

import Control.Monad.State

-- import Debug.Trace

-- Note [Parser monad]
--
-- For reference,
--
-- in *parsec*, the base monad transformer is
--
-- ParsecT s u m a
--
-- where
--
--   s   is the input stream type
--   u   is the user state type
--   m   is the underlying monad
--   a   is the return type
--
-- whereas in *megaparsec*, the base monad transformer is
--
-- ParsecT e s m a
--
-- where
--
--   e   is the custom data component for errors
--   s   is the input stream type
--   m   is the underlying monad
--   a   is the return type
--
-- The Liquid Haskell parser tracks state in 'PState', primarily
-- for operator fixities.
--
-- The old Liquid Haskell parser did not use parsec's "user state"
-- functionality for 'PState', but instead wrapped a state monad
-- in a parsec monad. We do the same thing for megaparsec.
--
-- However, user state was still used for an additional 'Integer'
-- as a unique supply. We incorporate this in the 'PState'.
--
-- Furthermore, we have to decide whether the state in the parser
-- should be "backtracking" or not. "Backtracking" state resets when
-- the parser backtracks, and thus only contains state modifications
-- performed by successful parses. On the other hand, non-backtracking
-- state would contain all modifications made during the parsing
-- process and allow us to observe unsuccessful attempts.
--
-- It turns out that:
--
-- - parsec's old built-in user state is backtracking
-- - using @StateT s (ParsecT ...)@ is backtracking
-- - using @ParsecT ... (StateT s ...)@ is non-backtracking
--
-- We want all our state to be backtracking.
--
-- Note that this is in deviation from what the old LH parser did,
-- but I think that was plainly wrong.

type Parser = StateT PState (Parsec Void String)

-- | The parser state.
--
-- We keep track of the fixities of infix operators.
--
-- We also keep track of whether empty list and singleton lists
-- syntax is allowed (and how they are to be interpreted, if they
-- are).
--
-- We also keep track of an integer counter that can be used to
-- supply unique integers during the parsing process.
--
-- Finally, we keep track of the layout stack.
--
data PState = PState { fixityTable :: OpTable
                     , fixityOps   :: [Fixity]
                     , empList     :: Maybe Expr
                     , singList    :: Maybe (Expr -> Expr)
                     , supply      :: !Integer
                     , layoutStack :: LayoutStack
                     }

-- | The layout stack tracks columns at which layout blocks
-- have started.
--
data LayoutStack =
    Empty -- ^ no layout info
  | Reset LayoutStack -- ^ in a block not using layout
  | At Pos LayoutStack -- ^ in a block at the given column
  | After Pos LayoutStack -- ^ past a block at the given column
  deriving Show

-- | Pop the topmost element from the stack.
popLayoutStack :: LayoutStack -> LayoutStack
popLayoutStack Empty       = error "unbalanced layout stack"
popLayoutStack (Reset s)   = s
popLayoutStack (At _ s)    = s
popLayoutStack (After _ s) = s

-- | Modify the layout stack using the given function.
modifyLayoutStack :: (LayoutStack -> LayoutStack) -> Parser ()
modifyLayoutStack f =
  modify (\ s -> s { layoutStack = f (layoutStack s) })

-- | Start a new layout block at the current indentation level.
setLayout :: Parser ()
setLayout = do
  i <- L.indentLevel
  -- traceShow ("setLayout", i) $ pure ()
  modifyLayoutStack (At i)

-- | Temporarily reset the layout information, because we enter
-- a block with explicit separators.
--
resetLayout :: Parser ()
resetLayout = do
  -- traceShow ("resetLayout") $ pure ()
  modifyLayoutStack Reset

-- | Remove the topmost element from the layout stack.
popLayout :: Parser ()
popLayout = do
  -- traceShow ("popLayout") $ pure ()
  modifyLayoutStack popLayoutStack

-- | Consumes all whitespace, including LH comments.
--
-- Should not be used directly, but primarily via 'lexeme'.
--
-- The only "valid" use case for spaces is in top-level parsing
-- function, to consume initial spaces.
--
spaces :: Parser ()
spaces =
  L.space
    space1
    lhLineComment
    lhBlockComment

-- | Verify that the current indentation level is in the given
-- relation to the provided reference level, otherwise fail.
--
-- This is a variant of 'indentGuard' provided by megaparsec,
-- only that it does not consume whitespace.
--
guardIndentLevel :: Ordering -> Pos -> Parser ()
guardIndentLevel ord ref = do
  actual <- L.indentLevel
  -- traceShow ("guardIndentLevel", actual, ord, ref) $ pure ()
  unless (compare actual ref == ord)
    (L.incorrectIndent ord ref actual)

-- | Checks the current indentation level with respect to the
-- current layout stack. May fail. Returns the parser to run
-- after the next token.
--
-- This function is intended to be used within a layout block
-- to check whether the next token is valid within the current
-- block.
--
guardLayout :: Parser (Parser ())
guardLayout = do
  stack <- gets layoutStack
  -- traceShow ("guardLayout", stack) $ pure ()
  case stack of
    At i s    -> guardIndentLevel EQ i *> pure (modifyLayoutStack (const (After i (At i s))))
      -- Note: above, we must really set the stack to 'After i (At i s)' explicitly.
      -- Otherwise, repeated calls to 'guardLayout' at the same column could push
      -- multiple 'After' entries on the stack.
    After i _ -> guardIndentLevel GT i *> pure (pure ())
    _         -> pure (pure ())

-- | Checks the current indentation level with respect to the
-- current layout stack. The current indentation level must
-- be strictly greater than the one of the surrounding block.
-- May fail.
--
-- This function is intended to be used before we establish
-- a new, nested, layout block, which should be indented further
-- than the surrounding blocks.
--
strictGuardLayout :: Parser ()
strictGuardLayout = do
  stack <- gets layoutStack
  -- traceShow ("strictGuardLayout", stack) $ pure ()
  case stack of
    At i _    -> guardIndentLevel GT i *> pure ()
    After i _ -> guardIndentLevel GT i *> pure ()
    _         -> pure ()


-- | Indentation-aware lexeme parser. Before parsing, establishes
-- whether we are in a position permitted by the layout stack.
-- After the token, consume whitespace and potentially change state.
--
lexeme :: Parser a -> Parser a
lexeme p = do
  after <- guardLayout
  p <* spaces <* after

-- | Indentation-aware located lexeme parser.
--
-- This is defined in such a way that it determines the actual source range
-- covered by the identifier. I.e., it consumes additional whitespace in the
-- end, but that is not part of the source range reported for the identifier.
--
locLexeme :: Parser a -> Parser (Located a)
locLexeme p = do
  after <- guardLayout
  l1 <- getSourcePos
  x <- p
  l2 <- getSourcePos
  spaces <* after
  pure (Loc l1 l2 x)

-- | Make a parser location-aware.
--
-- This is at the cost of an imprecise span because we still
-- consume spaces in the end first.
--
located :: Parser a -> Parser (Located a)
located p = do
  l1 <- getSourcePos
  x <- p
  l2 <- getSourcePos
  pure (Loc l1 l2 x)

-- | Parse a block delimited by layout.
-- The block must be indented more than the surrounding blocks,
-- otherwise we return an empty list.
--
-- Assumes that the parser for items does not accept the empty string.
--
indentedBlock :: Parser a -> Parser [a]
indentedBlock p =
      strictGuardLayout *> setLayout *> many (p <* popLayout) <* popLayout
      -- We have to pop after every p, because the first successful
      -- token moves from 'At' to 'After'. We have to pop at the end,
      -- because we want to remove 'At'.
  <|> pure []
      -- We need to have a fallback with the empty list, because if the
      -- layout check fails, we still want to accept this as an empty block.

-- | Parse a single line that may be continued via layout.
indentedLine :: Parser a -> Parser a
indentedLine p =
  setLayout *> p <* popLayout <* popLayout
  -- We have to pop twice, because the first successful token
  -- moves from 'At' to 'After', so we have to remove both.

-- | Parse a block of items which can be delimited either via
-- layout or via explicit delimiters as specified.
--
-- Assumes that the parser for items does not accept the empty string.
--
indentedOrExplicitBlock :: Parser open -> Parser close -> Parser sep -> Parser a -> Parser [a]
indentedOrExplicitBlock open close sep p =
      explicitBlock open close sep p
  <|> (concat <$> indentedBlock (sepEndBy1 p sep))

-- | Parse a block of items that are delimited via explicit delimiters.
-- Layout is disabled/reset for the scope of this block.
--
explicitBlock :: Parser open -> Parser close -> Parser sep -> Parser a -> Parser [a]
explicitBlock open close sep p =
  resetLayout *> open *> sepEndBy p sep <* close <* popLayout

-- | Symbolic lexeme. Stands on its own.
sym :: String -> Parser String
sym x =
  lexeme (string x)

-- | Located variant of 'sym'.
locSym :: String -> Parser (Located String)
locSym x =
  locLexeme (string x)

semi, comma, colon, dcolon, dot :: Parser String
semi   = sym ";"
comma  = sym ","
colon  = sym ":" -- Note: not a reserved symbol; use with care
dcolon = sym "::" -- Note: not a reserved symbol; use with care
dot    = sym "." -- Note: not a reserved symbol; use with care

-- | Parses a block via layout or explicit braces and semicolons.
--
-- Assumes that the parser for items does not accept the empty string.
--
-- However, even in layouted mode, we are allowing semicolons to
-- separate block contents. We also allow semicolons at the beginning,
-- end, and multiple subsequent semicolons, so the resulting parser
-- provides the illusion of allowing empty items.
--
block :: Parser a -> Parser [a]
block =
  indentedOrExplicitBlock (sym "{" *> many semi) (sym "}") (some semi)

-- | Parses a block with explicit braces and commas as separator.
-- Used for record constructors in datatypes.
--
explicitCommaBlock :: Parser a -> Parser [a]
explicitCommaBlock =
  explicitBlock (sym "{") (sym "}") comma

--------------------------------------------------------------------

reservedNames :: S.HashSet String
reservedNames = S.fromList
  [ -- reserved words used in fixpoint
    "SAT"
  , "UNSAT"
  , "true"
  , "false"
  , "mod"
  , "data"
  , "Bexp"
  -- , "True"
  -- , "Int"
  , "import"
  , "if", "then", "else"
  , "func"
  , "autorewrite"
  , "rewrite"

  -- reserved words used in liquid haskell
  , "forall"
  , "coerce"
  , "exists"
  , "module"
  , "spec"
  , "where"
  , "decrease"
  , "lazyvar"
  , "LIQUID"
  , "lazy"
  , "local"
  , "assert"
  , "assume"
  , "automatic-instances"
  , "autosize"
  , "axiomatize"
  , "bound"
  , "class"
  , "data"
  , "define"
  , "defined"
  , "embed"
  , "expression"
  , "import"
  , "include"
  , "infix"
  , "infixl"
  , "infixr"
  , "inline"
  , "instance"
  , "invariant"
  , "measure"
  , "newtype"
  , "predicate"
  , "qualif"
  , "reflect"
  , "type"
  , "using"
  , "with"
  , "in"
  ]

-- TODO: This is currently unused.
--
-- The only place where this is used in the original parsec code is in the
-- Text.Parsec.Token.operator parser.
--
_reservedOpNames :: [String]
_reservedOpNames =
  [ "+", "-", "*", "/", "\\", ":"
  , "<", ">", "<=", ">=", "=", "!=" , "/="
  , "mod", "and", "or"
  --, "is"
  , "&&", "||"
  , "~", "=>", "==>", "<=>"
  , "->"
  , ":="
  , "&", "^", "<<", ">>", "--"
  , "?", "Bexp"
  , "'"
  , "_|_"
  , "|"
  , "<:"
  , "|-"
  , "::"
  , "."
  ]

{-
lexer :: Monad m => Token.GenTokenParser String u m
lexer = Token.makeTokenParser languageDef
-}

-- | Consumes a line comment.
lhLineComment :: Parser ()
lhLineComment =
  L.skipLineComment "// "

-- | Consumes a block comment.
lhBlockComment :: Parser ()
lhBlockComment =
  L.skipBlockComment "/* " "*/"

-- | Parser that consumes a single char within an identifier (not start of identifier).
identLetter :: Parser Char
identLetter =
  alphaNumChar <|> oneOf ("_" :: String)

-- | Parser that consumes a single char within an operator (not start of operator).
opLetter :: Parser Char
opLetter =
  oneOf (":!#$%&*+./<=>?@\\^|-~'" :: String)

-- | Parser that consumes the given reserved word.
--
-- The input token cannot be longer than the given name.
--
-- NOTE: we currently don't double-check that the reserved word is in the
-- list of reserved words.
--
reserved :: String -> Parser ()
reserved x =
  void $ lexeme (try (string x <* notFollowedBy identLetter))

locReserved :: String -> Parser (Located String)
locReserved x =
  locLexeme (try (string x <* notFollowedBy identLetter))

-- | Parser that consumes the given reserved operator.
--
-- The input token cannot be longer than the given name.
--
-- NOTE: we currently don't double-check that the reserved operator is in the
-- list of reserved operators.
--
reservedOp :: String -> Parser ()
reservedOp x =
  void $ lexeme (try (string x <* notFollowedBy opLetter))

-- | Parser that consumes the given symbol.
--
-- The difference with 'reservedOp' is that the given symbol is seen
-- as a token of its own, so the next character that follows does not
-- matter.
--
-- symbol :: String -> Parser String
-- symbol x =
--   L.symbol spaces (string x)

parens, brackets, angles, braces :: Parser a -> Parser a
parens   = between (sym "(") (sym ")")
brackets = between (sym "[") (sym "]")
angles   = between (sym "<") (sym ">")
braces   = between (sym "{") (sym "}")

locParens :: Parser a -> Parser (Located a)
locParens p =
  (\ (Loc l1 _ _) a (Loc _ l2 _) -> Loc l1 l2 a) <$> locSym "(" <*> p <*> locSym ")"

-- | Parses a string literal as a lexeme. This is based on megaparsec's
-- 'charLiteral' parser, which claims to handle all the single-character
-- escapes defined by the Haskell grammar.
--
stringLiteral :: Parser String
stringLiteral =
  lexeme stringR <?> "string literal"

locStringLiteral :: Parser (Located String)
locStringLiteral =
  locLexeme stringR <?> "string literal"

stringR :: Parser String
stringR =
  char '\"' *> manyTill L.charLiteral (char '\"')

-- | Consumes a float literal lexeme.
double :: Parser Double
double = lexeme L.float <?> "float literal"

-- identifier :: Parser String
-- identifier = Token.identifier lexer

-- | Consumes a natural number literal lexeme, which can be
-- in decimal, octal and hexadecimal representation.
--
-- This does not parse negative integers. Unary minus is available
-- as an operator in the expression language.
--
natural :: Parser Integer
natural =
  lexeme naturalR <?> "nat literal"

locNatural :: Parser (Located Integer)
locNatural =
  locLexeme naturalR <?> "nat literal"

naturalR :: Parser Integer
naturalR =
      try (char '0' *> char' 'x') *> L.hexadecimal
  <|> try (char '0' *> char' 'o') *> L.octal
  <|> L.decimal

-- | Raw (non-whitespace) parser for an identifier adhering to certain conditions.
--
-- The arguments are as follows, in order:
--
-- * the parser for the initial character,
-- * a predicate indicating which subsequent characters are ok,
-- * a check for the entire identifier to be applied in the end,
-- * an error message to display if the final check fails.
--
condIdR :: Parser Char -> (Char -> Bool) -> (String -> Bool) -> String -> Parser Symbol
condIdR initial okChars condition msg = do
  s <- (:) <$> initial <*> takeWhileP Nothing okChars
  if condition s
    then pure (symbol s)
    else fail (msg <> " " <> show s)

-- TODO: The use of the following parsers is unsystematic.

-- | Raw parser for an identifier starting with an uppercase letter.
--
-- See Note [symChars].
--
upperIdR :: Parser Symbol
upperIdR =
  condIdR upperChar (`S.member` symChars) (const True) "unexpected"

-- | Raw parser for an identifier starting with a lowercase letter.
--
-- See Note [symChars].
--
lowerIdR :: Parser Symbol
lowerIdR =
  condIdR (lowerChar <|> char '_') (`S.member` symChars) isNotReserved "unexpected reserved word"

-- | Raw parser for an identifier starting with any letter.
--
-- See Note [symChars].
--
symbolR :: Parser Symbol
symbolR =
  condIdR (letterChar <|> char '_') (`S.member` symChars) isNotReserved "unexpected reserved word"

isNotReserved :: String -> Bool
isNotReserved s = not (s `S.member` reservedNames)

-- | Predicate version to check if the characer is a valid initial
-- character for 'lowerIdR'.
--
-- TODO: What is this needed for?
--
isSmall :: Char -> Bool
isSmall c = Char.isLower c || c == '_'

-- Note [symChars].
--
-- The parser 'symChars' is very permissive. In particular, we allow
-- dots (for qualified names), and characters such as @$@ to be able
-- to refer to identifiers as they occur in e.g. GHC Core.

----------------------------------------------------------------
------------------------- Expressions --------------------------
----------------------------------------------------------------

-- | Lexeme version of 'upperIdR'.
--
upperIdP :: Parser Symbol
upperIdP  =
  lexeme upperIdR <?> "upperIdP"

-- | Lexeme version of 'lowerIdR'.
--
lowerIdP :: Parser Symbol
lowerIdP  =
  lexeme lowerIdR <?> "lowerIdP"

-- | Unconstrained identifier, lower- or uppercase.
--
-- Must not be a reserved word.
--
-- Lexeme version of 'symbolR'.
--
symbolP :: Parser Symbol
symbolP =
  lexeme symbolR <?> "identifier"

-- The following are located versions of the lexeme identifier parsers.

locSymbolP, locLowerIdP, locUpperIdP :: Parser LocSymbol
locLowerIdP = locLexeme lowerIdR
locUpperIdP = locLexeme upperIdR
locSymbolP  = locLexeme symbolR

-- | Parser for literal numeric constants: floats or integers without sign.
constantP :: Parser Constant
constantP =
     try (R <$> double)   -- float literal
 <|> I <$> natural        -- nat literal

-- | Parser for literal string contants.
symconstP :: Parser SymConst
symconstP = SL . T.pack <$> stringLiteral

-- | Parser for "atomic" expressions.
--
-- This parser is reused by Liquid Haskell.
--
expr0P :: Parser Expr
expr0P
  =  trueP -- constant "true"
 <|> falseP -- constant "false"
 <|> fastIfP EIte exprP -- "if-then-else", starts with "if"
 <|> coerceP exprP -- coercion, starts with "coerce"
 <|> (ESym <$> symconstP) -- string literal, starts with double-quote
 <|> (ECon <$> constantP) -- numeric literal, starts with a digit
 <|> (reservedOp "_|_" >> return EBot) -- constant bottom, equivalent to "false"
 <|> lamP -- lambda abstraction, starts with backslash
 <|> try tupleP -- tuple expressions, starts with "("
 <|> try (parens exprP) -- parenthesised expression, starts with "("
 <|> try (parens exprCastP) -- explicit type annotation, starts with "(", TODO: should be an operator rather than require parentheses?
 <|> EVar <$> symbolP -- identifier, starts with any letter or underscore
 <|> try (brackets (pure ()) >> emptyListP) -- empty list, start with "["
 <|> try (brackets exprP >>= singletonListP) -- singleton list, starts with "["
 --
 -- Note:
 --
 -- In the parsers above, it is important that *all* parsers starting with "("
 -- are prefixed with "try". This is because expr0P itself is chained with
 -- additional parsers in funAppP ...

emptyListP :: Parser Expr
emptyListP = do
  e <- empList <$> get
  case e of
    Nothing -> fail "No parsing support for empty lists"
    Just s  -> return s

singletonListP :: Expr -> Parser Expr
singletonListP e = do
  f <- singList <$> get
  case f of
    Nothing -> fail "No parsing support for singleton lists"
    Just s  -> return $ s e

-- | Parser for an explicitly type-annotated expression.
exprCastP :: Parser Expr
exprCastP
  = do e  <- exprP
       try dcolon <|> colon -- allow : or :: *and* allow following symbols
       so <- sortP
       return $ ECst e so

fastIfP :: (Expr -> a -> a -> a) -> Parser a -> Parser a
fastIfP f bodyP
  = do reserved "if"
       p <- predP
       reserved "then"
       b1 <- bodyP
       reserved "else"
       b2 <- bodyP
       return $ f p b1 b2

coerceP :: Parser Expr -> Parser Expr
coerceP p = do
  reserved "coerce"
  (s, t) <- parens (pairP sortP (reservedOp "~") sortP)
  e      <- p
  return $ ECoerc s t e



{-
qmIfP f bodyP
  = parens $ do
      p  <- predP
      reserved "?"
      b1 <- bodyP
      colon
      b2 <- bodyP
      return $ f p b1 b2
-}

-- | Parser for atomic expressions plus function applications.
--
-- Base parser used in 'exprP' which adds in other operators.
--
expr1P :: Parser Expr
expr1P
  =  try funAppP
 <|> expr0P

-- | Expressions
exprP :: Parser Expr
exprP =
  do
    table <- gets fixityTable
    makeExprParser expr1P (flattenOpTable table)

data Assoc = AssocNone | AssocLeft | AssocRight

data Fixity
  = FInfix   {fpred :: Maybe Int, fname :: String, fop2 :: Maybe (Expr -> Expr -> Expr), fassoc :: Assoc}
  | FPrefix  {fpred :: Maybe Int, fname :: String, fop1 :: Maybe (Expr -> Expr)}
  | FPostfix {fpred :: Maybe Int, fname :: String, fop1 :: Maybe (Expr -> Expr)}


-- | An OpTable stores operators by their fixity.
--
-- Fixity levels range from 9 (highest) to 0 (lowest).
type OpTable = IM.IntMap [Operator Parser Expr] -- [[Operator Parser Expr]]

-- | Transform an operator table to the form expected by 'makeExprParser',
-- which wants operators sorted by decreasing priority.
--
flattenOpTable :: OpTable -> [[Operator Parser Expr]]
flattenOpTable =
  (snd <$>) <$> IM.toDescList

-- | Add an operator to the parsing state.
addOperatorP :: Fixity -> Parser ()
addOperatorP op
  = modify $ \s -> s{ fixityTable = addOperator op (fixityTable s)
                    , fixityOps   = op:fixityOps s
                    }

-- | Parses any of the known infix operators.
infixSymbolP :: Parser Symbol
infixSymbolP = do
  ops <- infixOps <$> get
  choice (reserved' <$> ops)
  where
    infixOps st = [s | FInfix _ s _ _ <- fixityOps st]
    reserved' x = reserved x >> return (symbol x)

-- | Located version of 'infixSymbolP'.
locInfixSymbolP :: Parser (Located Symbol)
locInfixSymbolP = do
  ops <- infixOps <$> get
  choice (reserved' <$> ops)
  where
    infixOps st = [s | FInfix _ s _ _ <- fixityOps st]
    reserved' x = locReserved x >>= \ (Loc l1 l2 _) -> return (Loc l1 l2 (symbol x))

-- | Helper function that turns an associativity into the right constructor for 'Operator'.
mkInfix :: Assoc -> parser (expr -> expr -> expr) -> Operator parser expr
mkInfix AssocLeft  = InfixL
mkInfix AssocRight = InfixR
mkInfix AssocNone  = InfixN

-- | Add the given operator to the operator table.
addOperator :: Fixity -> OpTable -> OpTable
addOperator (FInfix p x f assoc) ops
 = insertOperator (makePrec p) (mkInfix assoc (reservedOp x >> return (makeInfixFun x f))) ops
addOperator (FPrefix p x f) ops
 = insertOperator (makePrec p) (Prefix (reservedOp x >> return (makePrefixFun x f))) ops
addOperator (FPostfix p x f) ops
 = insertOperator (makePrec p) (Postfix (reservedOp x >> return (makePrefixFun x f))) ops

-- | Helper function for computing the priority of an operator.
--
-- If no explicit priority is given, a priority of 9 is assumed.
--
makePrec :: Maybe Int -> Int
makePrec = fromMaybe 9

makeInfixFun :: String -> Maybe (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
makeInfixFun x = fromMaybe (\e1 e2 -> EApp (EApp (EVar $ symbol x) e1) e2)

makePrefixFun :: String -> Maybe (Expr -> Expr) -> Expr -> Expr
makePrefixFun x = fromMaybe (EApp (EVar $ symbol x))

-- | Add an operator at the given priority to the operator table.
insertOperator :: Int -> Operator Parser Expr -> OpTable -> OpTable
insertOperator i op = IM.alter (Just . (op :) . fromMaybe []) i

-- | The initial (empty) operator table.
initOpTable :: OpTable
initOpTable = IM.empty

-- | Built-in operator table, parameterised over the composition function.
bops :: Maybe Expr -> OpTable
bops cmpFun = foldl' (flip addOperator) initOpTable builtinOps
  where
    -- Built-in Haskell operators, see https://www.haskell.org/onlinereport/decls.html#fixity
    builtinOps :: [Fixity]
    builtinOps = [ FPrefix (Just 9) "-"   (Just ENeg)
                 , FInfix  (Just 7) "*"   (Just $ EBin Times) AssocLeft
                 , FInfix  (Just 7) "/"   (Just $ EBin Div)   AssocLeft
                 , FInfix  (Just 6) "-"   (Just $ EBin Minus) AssocLeft
                 , FInfix  (Just 6) "+"   (Just $ EBin Plus)  AssocLeft
                 , FInfix  (Just 5) "mod" (Just $ EBin Mod)   AssocLeft -- Haskell gives mod 7
                 , FInfix  (Just 9) "."   applyCompose        AssocRight
                 ]
    applyCompose :: Maybe (Expr -> Expr -> Expr)
    applyCompose = (\f x y -> (f `eApps` [x,y])) <$> cmpFun

-- | Parser for function applications.
--
-- Andres, TODO: Why is this so complicated?
--
funAppP :: Parser Expr
funAppP            =  litP <|> exprFunP <|> simpleAppP
  where
    exprFunP = mkEApp <$> funSymbolP <*> funRhsP
    funRhsP  =  some expr0P
            <|> parens innerP
    innerP   = brackets (sepBy exprP semi)

    -- TODO:AZ the parens here should be superfluous, but it hits an infinite loop if removed
    simpleAppP     = EApp <$> parens exprP <*> parens exprP
    funSymbolP     = locSymbolP

-- | Parser for tuple expressions (two or more components).
tupleP :: Parser Expr
tupleP = do
  Loc l1 l2 (first, rest) <- locParens ((,) <$> exprP <* comma <*> sepBy1 exprP comma) -- at least two components necessary
  let cons = symbol $ "(" ++ replicate (length rest) ',' ++ ")" -- stored in prefix form
  return $ mkEApp (Loc l1 l2 cons) (first : rest)


-- TODO:AZ: The comment says BitVector literal, but it accepts any @Sort@
-- | BitVector literal: lit "#x00000001" (BitVec (Size32 obj))
litP :: Parser Expr
litP = do reserved "lit"
          l <- stringLiteral
          t <- sortP
          return $ ECon $ L (T.pack l) t

-- | Parser for lambda abstractions.
lamP :: Parser Expr
lamP
  = do reservedOp "\\"
       x <- symbolP
       colon -- TODO: this should probably be reservedOp instead
       t <- sortP
       reservedOp "->"
       e  <- exprP
       return $ ELam (x, t) e

varSortP :: Parser Sort
varSortP  = FVar  <$> parens intP

-- | Parser for function sorts without the "func" keyword.
funcSortP :: Parser Sort
funcSortP = parens $ mkFFunc <$> intP <* comma <*> sortsP

sortsP :: Parser [Sort]
sortsP = try (brackets (sepBy sortP semi)) 
      <|> (brackets (sepBy sortP comma)) 

-- | Parser for sorts (types).
sortP    :: Parser Sort
sortP    = sortP' (many sortArgP)

sortArgP :: Parser Sort
sortArgP = sortP' (return [])

{-
sortFunP :: Parser Sort
sortFunP
   =  try (string "@" >> varSortP)
  <|> (fTyconSort <$> fTyConP)
-}

-- | Parser for sorts, parameterised over the parser for arguments.
--
-- TODO, Andres: document the parameter better.
--
sortP' :: Parser [Sort] -> Parser Sort
sortP' appArgsP
   =  parens sortP -- parenthesised sort, starts with "("
  <|> (reserved "func" >> funcSortP) -- function sort, starts with "func"
  <|> (fAppTC listFTyCon . pure <$> brackets sortP)
  -- <|> bvSortP -- Andres: this looks unreachable, as it starts with "("
  <|> (fAppTC <$> fTyConP <*> appArgsP)
  <|> (fApp   <$> tvarP   <*> appArgsP)

tvarP :: Parser Sort
tvarP
   =  (string "@" >> varSortP)
  <|> (FObj . symbol <$> lowerIdP)


fTyConP :: Parser FTycon
fTyConP
  =   (reserved "int"     >> return intFTyCon)
  <|> (reserved "Integer" >> return intFTyCon)
  <|> (reserved "Int"     >> return intFTyCon)
  -- <|> (reserved "int"     >> return intFTyCon) -- TODO:AZ duplicate?
  <|> (reserved "real"    >> return realFTyCon)
  <|> (reserved "bool"    >> return boolFTyCon)
  <|> (reserved "num"     >> return numFTyCon)
  <|> (reserved "Str"     >> return strFTyCon)
  <|> (symbolFTycon      <$> locUpperIdP)

-- | Bit-Vector Sort
bvSortP :: Parser Sort
bvSortP = mkSort <$> (bvSizeP "Size32" S32 <|> bvSizeP "Size64" S64)
  where
    bvSizeP ss s = do
      parens (reserved "BitVec" >> reserved ss)
      return s


--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Parser for "atomic" predicates.
--
-- This parser is reused by Liquid Haskell.
--
pred0P :: Parser Expr
pred0P =  trueP -- constant "true"
      <|> falseP -- constant "false"
      <|> (reservedOp "??" >> makeUniquePGrad)
      <|> kvarPredP
      <|> fastIfP pIte predP -- "if-then-else", starts with "if"
      <|> try predrP -- binary relation, starts with anything that an expr can start with
      <|> (parens predP) -- parenthesised predicate, starts with "("
      <|> (reservedOp "?" *> exprP)
      <|> try funAppP
      <|> EVar <$> symbolP -- identifier, starts with any letter or underscore
      <|> (reservedOp "&&" >> pGAnds <$> predsP) -- built-in prefix and
      <|> (reservedOp "||" >> POr  <$> predsP) -- built-in prefix or

makeUniquePGrad :: Parser Expr
makeUniquePGrad
  = do uniquePos <- getSourcePos
       return $ PGrad (KV $ symbol $ show uniquePos) mempty (srcGradInfo uniquePos) mempty

-- qmP    = reserved "?" <|> reserved "Bexp"

-- | Parser for the reserved constant "true".
trueP :: Parser Expr
trueP  = reserved "true"  >> return PTrue

-- | Parser for the reserved constant "false".
falseP :: Parser Expr
falseP = reserved "false" >> return PFalse

kvarPredP :: Parser Expr
kvarPredP = PKVar <$> kvarP <*> substP

kvarP :: Parser KVar
kvarP = KV <$> lexeme (char '$' *> symbolR)

substP :: Parser Subst
substP = mkSubst <$> many (brackets $ pairP symbolP aP exprP)
  where
    aP = reservedOp ":="

-- | Parses a semicolon-separated bracketed list of predicates.
--
-- Used as the argument of the prefix-versions of conjunction and
-- disjunction.
--
predsP :: Parser [Expr]
predsP = brackets $ sepBy predP semi

-- | Parses a predicate.
--
-- Unlike for expressions, there is a built-in operator list.
--
predP  :: Parser Expr
predP  = makeExprParser pred0P lops
  where
    lops = [ [Prefix (reservedOp "~"    >> return PNot)]
           , [Prefix (reserved   "not"  >> return PNot)]
           , [InfixR (reservedOp "&&"   >> return pGAnd)]
           , [InfixR (reservedOp "||"   >> return (\x y -> POr [x,y]))]
           , [InfixR (reservedOp "=>"   >> return PImp)]
           , [InfixR (reservedOp "==>"  >> return PImp)]
           , [InfixR (reservedOp "="    >> return PIff)]
           , [InfixR (reservedOp "<=>"  >> return PIff)]]

-- | Parses a relation predicate.
--
-- Binary relations connect expressions and predicates.
--
predrP :: Parser Expr
predrP =
  (\ e1 r e2 -> r e1 e2) <$> exprP <*> brelP <*> exprP

-- | Parses a relation symbol.
--
-- There is a built-in table of available relations.
--
brelP ::  Parser (Expr -> Expr -> Expr)
brelP =  (reservedOp "==" >> return (PAtom Eq))
     <|> (reservedOp "="  >> return (PAtom Eq))
     <|> (reservedOp "~~" >> return (PAtom Ueq))
     <|> (reservedOp "!=" >> return (PAtom Ne))
     <|> (reservedOp "/=" >> return (PAtom Ne))
     <|> (reservedOp "!~" >> return (PAtom Une))
     <|> (reservedOp "<"  >> return (PAtom Lt))
     <|> (reservedOp "<=" >> return (PAtom Le))
     <|> (reservedOp ">"  >> return (PAtom Gt))
     <|> (reservedOp ">=" >> return (PAtom Ge))

--------------------------------------------------------------------------------
-- | BareTypes -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Refa
refaP :: Parser Expr
refaP =  try (pAnd <$> brackets (sepBy predP semi))
     <|> predP


-- | (Sorted) Refinements with configurable sub-parsers
refBindP :: Parser Symbol -> Parser Expr -> Parser (Reft -> a) -> Parser a
refBindP bp rp kindP
  = braces $ do
      x  <- bp
      t  <- kindP
      reservedOp "|"
      ra <- rp <* spaces
      return $ t (Reft (x, ra))


-- bindP      = symbol    <$> (lowerIdP <* colon)
-- | Binder (lowerIdP <* colon)
bindP :: Parser Symbol
bindP = symbolP <* colon

optBindP :: Symbol -> Parser Symbol
optBindP x = try bindP <|> return x

-- | (Sorted) Refinements
refP :: Parser (Reft -> a) -> Parser a
refP       = refBindP bindP refaP

-- | (Sorted) Refinements with default binder
refDefP :: Symbol -> Parser Expr -> Parser (Reft -> a) -> Parser a
refDefP x  = refBindP (optBindP x)

--------------------------------------------------------------------------------
-- | Parsing Data Declarations -------------------------------------------------
--------------------------------------------------------------------------------

dataFieldP :: Parser DataField
dataFieldP = DField <$> locSymbolP <* colon <*> sortP

dataCtorP :: Parser DataCtor
dataCtorP  = DCtor <$> locSymbolP
                   <*> braces (sepBy dataFieldP comma)

dataDeclP :: Parser DataDecl
dataDeclP  = DDecl <$> fTyConP <*> intP <* reservedOp "="
                   <*> brackets (many (reservedOp "|" *> dataCtorP))

--------------------------------------------------------------------------------
-- | Parsing Qualifiers --------------------------------------------------------
--------------------------------------------------------------------------------

-- | Qualifiers
qualifierP :: Parser Sort -> Parser Qualifier
qualifierP tP = do
  pos    <- getSourcePos
  n      <- upperIdP
  params <- parens $ sepBy1 (qualParamP tP) comma
  _      <- colon
  body   <- predP
  return  $ mkQual n params body pos

qualParamP :: Parser Sort -> Parser QualParam
qualParamP tP = do
  x     <- symbolP
  pat   <- qualPatP
  _     <- colon
  t     <- tP
  return $ QP x pat t

qualPatP :: Parser QualPattern
qualPatP
   =  (reserved "as" >> qualStrPatP)
  <|> return PatNone

qualStrPatP :: Parser QualPattern
qualStrPatP
   = (PatExact <$> symbolP)
  <|> parens (    (uncurry PatPrefix <$> pairP symbolP dot qpVarP)
              <|> (uncurry PatSuffix <$> pairP qpVarP  dot symbolP) )


qpVarP :: Parser Int
qpVarP = char '$' *> intP

symBindP :: Parser a -> Parser (Symbol, a)
symBindP = pairP symbolP colon

pairP :: Parser a -> Parser z -> Parser b -> Parser (a, b)
pairP xP sepP yP = (,) <$> xP <* sepP <*> yP

---------------------------------------------------------------------
-- | Axioms for Symbolic Evaluation ---------------------------------
---------------------------------------------------------------------

autoRewriteP :: Parser AutoRewrite
autoRewriteP = do
  args       <- sepBy sortedReftP spaces
  _          <- spaces
  _          <- reserved "="
  _          <- spaces
  (lhs, rhs) <- braces $
      pairP exprP (reserved "=") exprP
  return $ AutoRewrite args lhs rhs


defineP :: Parser Equation
defineP = do
  name   <- symbolP
  params <- parens        $ sepBy (symBindP sortP) comma
  sort   <- colon        *> sortP
  body   <- reserved "=" *> braces (
              if sort == boolSort then predP else exprP
               )
  return  $ mkEquation name params body sort

matchP :: Parser Rewrite
matchP = SMeasure <$> symbolP <*> symbolP <*> many symbolP <*> (reserved "=" >> exprP)

pairsP :: Parser a -> Parser b -> Parser [(a, b)]
pairsP aP bP = brackets $ sepBy1 (pairP aP (reserved ":") bP) semi
---------------------------------------------------------------------
-- | Parsing Constraints (.fq files) --------------------------------
---------------------------------------------------------------------

-- Entities in Query File
data Def a
  = Srt !Sort
  | Cst !(SubC a)
  | Wfc !(WfC a)
  | Con !Symbol !Sort
  | Dis !Symbol !Sort
  | Qul !Qualifier
  | Kut !KVar
  | Pack !KVar !Int
  | IBind !Int !Symbol !SortedReft
  | EBind !Int !Symbol !Sort
  | Opt !String
  | Def !Equation
  | Mat !Rewrite
  | Expand ![(Int,Bool)]
  | Adt  !DataDecl
  | AutoRW !Int !AutoRewrite
  | RWMap ![(Int,Int)]
  deriving (Show, Generic)
  --  Sol of solbind
  --  Dep of FixConstraint.dep

fInfoOptP :: Parser (FInfoWithOpts ())
fInfoOptP = do ps <- many defP
               return $ FIO (defsFInfo ps) [s | Opt s <- ps]

fInfoP :: Parser (FInfo ())
fInfoP = defsFInfo <$> {- SCC "many-defP" #-} many defP

defP :: Parser (Def ())
defP =  Srt   <$> (reserved "sort"         >> colon >> sortP)
    <|> Cst   <$> (reserved "constraint"   >> colon >> {- SCC "subCP" #-} subCP)
    <|> Wfc   <$> (reserved "wf"           >> colon >> {- SCC "wfCP"  #-} wfCP)
    <|> Con   <$> (reserved "constant"     >> symbolP) <*> (colon >> sortP)
    <|> Dis   <$> (reserved "distinct"     >> symbolP) <*> (colon >> sortP)
    <|> Pack  <$> (reserved "pack"         >> kvarP)   <*> (colon >> intP)
    <|> Qul   <$> (reserved "qualif"       >> qualifierP sortP)
    <|> Kut   <$> (reserved "cut"          >> kvarP)
    <|> EBind <$> (reserved "ebind"        >> intP) <*> symbolP <*> (colon >> braces sortP)
    <|> IBind <$> (reserved "bind"         >> intP) <*> symbolP <*> (colon >> sortedReftP)
    <|> Opt    <$> (reserved "fixpoint"    >> stringLiteral)
    <|> Def    <$> (reserved "define"      >> defineP)
    <|> Mat    <$> (reserved "match"       >> matchP)
    <|> Expand <$> (reserved "expand"      >> pairsP intP boolP)
    <|> Adt    <$> (reserved "data"        >> dataDeclP)
    <|> AutoRW <$> (reserved "autorewrite" >> intP) <*> autoRewriteP
    <|> RWMap  <$> (reserved "rewrite"     >> pairsP intP intP)


sortedReftP :: Parser SortedReft
sortedReftP = refP (RR <$> (sortP <* spaces))

wfCP :: Parser (WfC ())
wfCP = do reserved "env"
          env <- envP
          reserved "reft"
          r   <- sortedReftP
          let [w] = wfC env r ()
          return w

subCP :: Parser (SubC ())
subCP = do pos <- getSourcePos
           reserved "env"
           env <- envP
           reserved "lhs"
           lhs <- sortedReftP
           reserved "rhs"
           rhs <- sortedReftP
           reserved "id"
           i   <- natural <* spaces
           tag <- tagP
           pos' <- getSourcePos
           return $ subC' env lhs rhs i tag pos pos'

subC' :: IBindEnv
      -> SortedReft
      -> SortedReft
      -> Integer
      -> Tag
      -> SourcePos
      -> SourcePos
      -> SubC ()
subC' env lhs rhs i tag l l'
  = case cs of
      [c] -> c
      _   -> die $ err sp $ "RHS without single conjunct at" <+> pprint l'
    where
       cs = subC env lhs rhs (Just i) tag ()
       sp = SS l l'


tagP  :: Parser [Int]
tagP  = reserved "tag" >> spaces >> brackets (sepBy intP semi)

envP  :: Parser IBindEnv
envP  = do binds <- brackets $ sepBy (intP <* spaces) semi
           return $ insertsIBindEnv binds emptyIBindEnv

intP :: Parser Int
intP = fromInteger <$> natural

boolP :: Parser Bool
boolP = (reserved "True" >> return True)
    <|> (reserved "False" >> return False)

defsFInfo :: [Def a] -> FInfo a
defsFInfo defs = {- SCC "defsFI" #-} FI cm ws bs ebs lts dts kts qs binfo adts mempty mempty ae
  where
    cm         = Misc.safeFromList
                   "defs-cm"        [(cid c, c)         | Cst c       <- defs]
    ws         = Misc.safeFromList
                   "defs-ws"        [(i, w)              | Wfc w    <- defs, let i = Misc.thd3 (wrft w)]
    bs         = bindEnvFromList  $ exBinds ++ [(n,x,r)  | IBind n x r <- defs]
    ebs        =                    [ n                  | (n,_,_) <- exBinds]
    exBinds    =                    [(n, x, RR t mempty) | EBind n x t <- defs]
    lts        = fromListSEnv       [(x, t)             | Con x t     <- defs]
    dts        = fromListSEnv       [(x, t)             | Dis x t     <- defs]
    kts        = KS $ S.fromList    [k                  | Kut k       <- defs]
    qs         =                    [q                  | Qul q       <- defs]
    binfo      = mempty
    expand     = M.fromList         [(fromIntegral i, f)| Expand fs   <- defs, (i,f) <- fs]
    eqs        =                    [e                  | Def e       <- defs]
    rews       =                    [r                  | Mat r       <- defs]
    autoRWs    = M.fromList         [(arId , s)         | AutoRW arId s <- defs]
    rwEntries  =                    [(i, f)             | RWMap fs   <- defs, (i,f) <- fs]
    rwMap      = foldl insert (M.fromList []) rwEntries
                 where
                   insert map (cid, arId) =
                     case M.lookup arId autoRWs of
                       Just rewrite ->
                         M.insertWith (++) (fromIntegral cid) [rewrite] map
                       Nothing ->
                         map
    cid        = fromJust . sid
    ae         = AEnv eqs rews expand rwMap
    adts       =                    [d                  | Adt d       <- defs]
    -- msg    = show $ "#Lits = " ++ (show $ length consts)

---------------------------------------------------------------------
-- | Interacting with Fixpoint --------------------------------------
---------------------------------------------------------------------

fixResultP :: Parser a -> Parser (FixResult a)
fixResultP pp
  =  (reserved "SAT"   >> return (Safe mempty))
 <|> (reserved "UNSAT" >> Unsafe mempty <$> brackets (sepBy pp comma))
 <|> (reserved "CRASH" >> crashP pp)

crashP :: Parser a -> Parser (FixResult a)
crashP pp = do
  i   <- pp
  msg <- takeWhileP Nothing (const True) -- consume the rest of the input
  return $ Crash [i] msg

predSolP :: Parser Expr
predSolP = parens (predP  <* (comma >> iQualP))

iQualP :: Parser [Symbol]
iQualP = upperIdP >> parens (sepBy symbolP comma)

solution1P :: Parser (KVar, Expr)
solution1P = do
  reserved "solution:"
  k  <- kvP
  reservedOp ":="
  ps <- brackets $ sepBy predSolP semi
  return (k, simplify $ PAnd ps)
  where
    kvP = try kvarP <|> (KV <$> symbolP)

solutionP :: Parser (M.HashMap KVar Expr)
solutionP = M.fromList <$> sepBy solution1P spaces

solutionFileP :: Parser (FixResult Integer, M.HashMap KVar Expr)
solutionFileP = (,) <$> fixResultP natural <*> solutionP

--------------------------------------------------------------------------------

-- | Parse via the given parser, and obtain the rest of the input
-- as well as the final source position.
--
remainderP :: Parser a -> Parser (a, String, SourcePos)
remainderP p
  = do res <- p
       str <- getInput
       pos <- getSourcePos
       return (res, str, pos)

-- | Initial parser state.
initPState :: Maybe Expr -> PState
initPState cmpFun = PState { fixityTable = bops cmpFun
                           , empList     = Nothing
                           , singList    = Nothing
                           , fixityOps   = []
                           , supply      = 0
                           , layoutStack = Empty
                           }

-- | Entry point for parsing, for testing.
--
-- Take the top-level parser, the source file name, and the input as a string.
-- Fails with an exception on a parse error.
--
doParse' :: Parser a -> SourceName -> String -> a
doParse' parser fileName input =
  case runParser (evalStateT (spaces *> parser <* eof) (initPState Nothing)) fileName input of
    Left peb@(ParseErrorBundle errors posState) -> -- parse errors; we extract the first error from the error bundle
      let
        ((_, pos) :| _, _) = attachSourcePos errorOffset errors posState
      in
        die $ err (SS pos pos) (dErr peb)
    Right r -> r -- successful parse with no remaining input
  where
    -- Turns the multiline error string from megaparsec into a pretty-printable Doc.
    dErr :: ParseErrorBundle String Void -> Doc
    dErr e = vcat (map text (lines (errorBundlePretty e)))

-- | Function to test parsers interactively.
parseTest' :: Show a => Parser a -> String -> IO ()
parseTest' parser input =
  parseTest (evalStateT parser (initPState Nothing)) input

-- errorSpan :: ParseError -> SrcSpan
-- errorSpan e = SS l l where l = errorPos e

parseFromFile :: Parser b -> SourceName -> IO b
parseFromFile p f = doParse' p f <$> readFile f

parseFromStdIn :: Parser a -> IO a
parseFromStdIn p = doParse' p "stdin" . T.unpack <$> T.getContents

-- | Obtain a fresh integer during the parsing process.
freshIntP :: Parser Integer
freshIntP = do n <- gets supply
               modify (\ s -> s{supply = n + 1})
               return n

---------------------------------------------------------------------
-- Standalone SMTLIB2 commands --------------------------------------
---------------------------------------------------------------------
commandsP :: Parser [Command]
commandsP = sepBy commandP semi

commandP :: Parser Command
commandP
  =  (reserved "var"      >> cmdVarP)
 <|> (reserved "push"     >> return Push)
 <|> (reserved "pop"      >> return Pop)
 <|> (reserved "check"    >> return CheckSat)
 <|> (reserved "assert"   >> (Assert Nothing <$> predP))
 <|> (reserved "distinct" >> (Distinct <$> brackets (sepBy exprP comma)))

cmdVarP :: Parser Command
cmdVarP = error "UNIMPLEMENTED: cmdVarP"
-- do
  -- x <- bindP
  -- t <- sortP
  -- return $ Declare x [] t

---------------------------------------------------------------------
-- Bundling Parsers into a Typeclass --------------------------------
---------------------------------------------------------------------

class Inputable a where
  rr  :: String -> a
  rr' :: String -> String -> a
  rr' _ = rr
  rr    = rr' ""

instance Inputable Symbol where
  rr' = doParse' symbolP

instance Inputable Constant where
  rr' = doParse' constantP

instance Inputable Expr where
  rr' = doParse' exprP

instance Inputable (FixResult Integer) where
  rr' = doParse' $ fixResultP natural

instance Inputable (FixResult Integer, FixSolution) where
  rr' = doParse' solutionFileP

instance Inputable (FInfo ()) where
  rr' = {- SCC "fInfoP" #-} doParse' fInfoP

instance Inputable (FInfoWithOpts ()) where
  rr' = {- SCC "fInfoWithOptsP" #-} doParse' fInfoOptP

instance Inputable Command where
  rr' = doParse' commandP

instance Inputable [Command] where
  rr' = doParse' commandsP

{-
---------------------------------------------------------------
--------------------------- Testing ---------------------------
---------------------------------------------------------------

-- A few tricky predicates for parsing
-- myTest1 = "((((v >= 56320) && (v <= 57343)) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o ((i - o) - 1)))) && (((numchars a o (i - (o -1))) >= 0) && (((i - o) - 1) >= 0)))) && ((not (((v >= 56320) && (v <= 57343)))) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o (i - o)))) && ((numchars a o (i - o)) >= 0))))"
--
-- myTest2 = "len x = len y - 1"
-- myTest3 = "len x y z = len a b c - 1"
-- myTest4 = "len x y z = len a b (c - 1)"
-- myTest5 = "x >= -1"
-- myTest6 = "(bLength v) = if n > 0 then n else 0"
-- myTest7 = "(bLength v) = (if n > 0 then n else 0)"
-- myTest8 = "(bLength v) = (n > 0 ? n : 0)"


sa  = "0"
sb  = "x"
sc  = "(x0 + y0 + z0) "
sd  = "(x+ y * 1)"
se  = "_|_ "
sf  = "(1 + x + _|_)"
sg  = "f(x,y,z)"
sh  = "(f((x+1), (y * a * b - 1), _|_))"
si  = "(2 + f((x+1), (y * a * b - 1), _|_))"

s0  = "true"
s1  = "false"
s2  = "v > 0"
s3  = "(0 < v && v < 100)"
s4  = "(x < v && v < y+10 && v < z)"
s6  = "[(v > 0)]"
s6' = "x"
s7' = "(x <=> y)"
s8' = "(x <=> a = b)"
s9' = "(x <=> (a <= b && b < c))"

s7  = "{ v: Int | [(v > 0)] }"
s8  = "x:{ v: Int | v > 0 } -> {v : Int | v >= x}"
s9  = "v = x+y"
s10 = "{v: Int | v = x + y}"

s11 = "x:{v:Int | true } -> {v:Int | true }"
s12 = "y : {v:Int | true } -> {v:Int | v = x }"
s13 = "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
s14 = "x:{v:a  | true} -> y:{v:b | true } -> {v:a | (x < v && v < y) }"
s15 = "x:Int -> Bool"
s16 = "x:Int -> y:Int -> {v:Int | v = x + y}"
s17 = "a"
s18 = "x:a -> Bool"
s20 = "forall a . x:Int -> Bool"

s21 = "x:{v : GHC.Prim.Int# | true } -> {v : Int | true }"

r0  = (rr s0) :: Pred
r0' = (rr s0) :: [Refa]
r1  = (rr s1) :: [Refa]


e1, e2  :: Expr
e1  = rr "(k_1 + k_2)"
e2  = rr "k_1"

o1, o2, o3 :: FixResult Integer
o1  = rr "SAT "
o2  = rr "UNSAT [1, 2, 9,10]"
o3  = rr "UNSAT []"

-- sol1 = doParse solution1P "solution: k_5 := [0 <= VV_int]"
-- sol2 = doParse solution1P "solution: k_4 := [(0 <= VV_int)]"

b0, b1, b2, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 :: BareType
b0  = rr "Int"
b1  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
b2  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}"
b4  = rr "forall a . x : a -> Bool"
b5  = rr "Int -> Int -> Int"
b6  = rr "(Int -> Int) -> Int"
b7  = rr "({v: Int | v > 10} -> Int) -> Int"
b8  = rr "(x:Int -> {v: Int | v > x}) -> {v: Int | v > 10}"
b9  = rr "x:Int -> {v: Int | v > x} -> {v: Int | v > 10}"
b10 = rr "[Int]"
b11 = rr "x:[Int] -> {v: Int | v > 10}"
b12 = rr "[Int] -> String"
b13 = rr "x:(Int, [Bool]) -> [(String, String)]"

-- b3 :: BareType
-- b3  = rr "x:Int -> y:Int -> {v:Bool | ((v is True) <=> x = y)}"

m1 = ["len :: [a] -> Int", "len (Nil) = 0", "len (Cons x xs) = 1 + len(xs)"]
m2 = ["tog :: LL a -> Int", "tog (Nil) = 100", "tog (Cons y ys) = 200"]

me1, me2 :: Measure.Measure BareType Symbol
me1 = (rr $ intercalate "\n" m1)
me2 = (rr $ intercalate "\n" m2)
-}
