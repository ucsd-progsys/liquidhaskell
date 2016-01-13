module Language.Haskell.Liquid.Unparse.Base (
    -- * The Unparse Typeclass
    Unparse(..)

    -- * Syntax Highlighting Colors
  , symbolToken, symbolToken'
  , keywordToken, keywordToken'
  , literalToken, literalToken'

    -- * Syntax Highlighting Utilities
    -- ** Literals
  , bool'
  , int'
  , integer'
  , float'
  , double'
  , stringLit
    -- ** Single Symbols
  , comma'
  , semi'
  , colon'
  , dot'
  , equals'
  , atSign
  , doubleEquals
  , notEquals
   -- ** Bracket Symbols
  , lparen', rparen'
  , langle', rangle'
  , lbrace', rbrace'
  , lbracket', rbracket'
    -- ** Bracketing
  , parens'
  , angles'
  , braces'
  , brackets'
    -- ** Misc
  ) where

import Text.PrettyPrint.ANSI.Leijen

--------------------------------------------------------------------------------
-- The Unparse Typeclass -------------------------------------------------------
--------------------------------------------------------------------------------

class Unparse a where
  unparse :: a -> Doc
  unparse = unparsePrec 0

  unparsePrec :: Int -> a -> Doc
  unparsePrec _ = unparse

  {-# MINIMAL unparse | unparsePrec #-}

instance Unparse Doc where
  unparse = id

--------------------------------------------------------------------------------
-- Syntax Highlighting Colors -------------------------------------------------
--------------------------------------------------------------------------------

symbolToken :: String -> Doc
symbolToken = symbolToken' . text

keywordToken :: String -> Doc
keywordToken = keywordToken' . text

literalToken :: String -> Doc
literalToken = literalToken' . text


symbolToken' :: Doc -> Doc
symbolToken' = yellow

keywordToken' :: Doc -> Doc
keywordToken' = blue

literalToken' :: Doc -> Doc
literalToken' = green

--------------------------------------------------------------------------------
-- Syntax Highlighting Utilities -----------------------------------------------
--------------------------------------------------------------------------------

-- Literals --------------------------------------------------------------------

bool' :: Bool -> Doc
bool' = literalToken' . bool

int' :: Int -> Doc
int' = literalToken' . int

integer' :: Integer -> Doc
integer' = literalToken' . integer

float' :: Float -> Doc
float' = literalToken' . float

double' :: Double -> Doc
double' = literalToken' . double

stringLit :: String -> Doc
stringLit = literalToken' . text . show

-- Single Sybmbols -------------------------------------------------------------

comma' :: Doc
comma' = symbolToken' comma

semi' :: Doc
semi' = symbolToken' semi

colon' :: Doc
colon' = symbolToken' colon

dot' :: Doc
dot' = symbolToken' dot

equals' :: Doc
equals' = symbolToken' equals


atSign :: Doc
atSign = symbolToken "@"

doubleEquals :: Doc
doubleEquals = symbolToken "=="

notEquals :: Doc
notEquals = symbolToken "/="

-- Bracket Symbols -------------------------------------------------------------

lparen' :: Doc
lparen' = symbolToken' lparen

rparen' :: Doc
rparen' = symbolToken' lparen

langle' :: Doc
langle' = symbolToken' langle

rangle' :: Doc
rangle' = symbolToken' rangle

lbrace' :: Doc
lbrace' = symbolToken' lbrace

rbrace' :: Doc
rbrace' = symbolToken' rbrace

lbracket' :: Doc
lbracket' = symbolToken' lbracket

rbracket' :: Doc
rbracket' = symbolToken' rbracket

-- Bracketing ------------------------------------------------------------------

parens' :: Doc -> Doc
parens' = enclose lparen' rparen'

angles' :: Doc -> Doc
angles' = enclose langle' rangle'

braces' :: Doc -> Doc
braces' = enclose lbrace' rbrace'

brackets' :: Doc -> Doc
brackets' = enclose lbracket' rbracket'

