{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Haskell.Liquid.PPrint2.Base (
    -- * Pretty-Printing Typeclass
    PPrint(..)

    -- * Annotating and Rendering
  , ADoc
  , TokenType(..)
  , symbolTok
  , keywordTok
  , literalTok
  , printColorized
  , hPrintColorized

    -- * Output Annotation Utilities
    -- ** Literals
  , intLit
  , integerLit
  , floatLit
  , doubleLit
  , stringLit
    -- ** Single Symbols
  , commaSym
  , semiSym
  , colonSym
  , dotSym
  , eqSym
  , atSym
  , doubleEqSym
  , notEqSym
   -- ** Bracket Symbols
  , lparenSym, rparenSym
  , langleSym, rangleSym
  , lbraceSym, rbraceSym
  , lbrackSym, rbrackSym
    -- ** Bracketing
  , wrapParens
  , wrapAngles
  , wrapBraces
  , wrapBrackets

    -- * Other Utility Functions
  , enclose
  , encloseSep
  ) where

import Control.Monad.State
import Control.Monad.Trans

import Data.Data
import Data.Typeable
import GHC.Generics

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import System.Console.ANSI
import System.IO

import Text.PrettyPrint.Annotated.HughesPJ

import Language.Fixpoint.Types (Symbol, symbolText)

import Language.Haskell.Liquid.Misc (tailOrEmpty)

--------------------------------------------------------------------------------
-- Pretty-Printing Typeclass ---------------------------------------------------
--------------------------------------------------------------------------------

class PPrint a where
  pprint :: a -> ADoc
  pprint = pprintPrec 0

  pprintPrec :: Int -> a -> ADoc
  pprintPrec _ = pprint

  {-# MINIMAL pprint | pprintPrec #-}

instance PPrint ADoc where
  pprint = id

instance PPrint String where
  pprint = text

instance PPrint T.Text where
  pprint = pprint . T.unpack

instance PPrint TL.Text where
  pprint = pprint . TL.unpack

instance PPrint Symbol where
  pprint = pprint . symbolText

instance PPrint Int where
  pprint = int

instance PPrint Integer where
  pprint = integer

instance PPrint Float where
  pprint = float

instance PPrint Double where
  pprint = double

--------------------------------------------------------------------------------
-- Annotating and Rendering ----------------------------------------------------
--------------------------------------------------------------------------------

type ADoc = Doc TokenType

data TokenType = Symbol | Keyword | Literal
                 deriving (Eq, Show, Data, Typeable, Generic)


symbolTok :: ADoc -> ADoc
symbolTok = annotate Symbol

keywordTok :: ADoc -> ADoc
keywordTok = annotate Keyword

literalTok :: ADoc -> ADoc
literalTok = annotate Literal


printColorized :: ADoc -> IO ()
printColorized = hPrintColorized stdout

hPrintColorized :: Handle -> ADoc -> IO ()
hPrintColorized h doc = evalStateT (doPrint doc) []
  where
    doPrint =
      renderDecoratedM startAnn endAnn printStr endDoc
    startAnn tok =
      modify (tok:) >> updateSGR
    endAnn _ =
      modify tailOrEmpty >> updateSGR
    printStr =
      liftIO . hPutStr h
    endDoc =
      put [] >> updateSGR
    updateSGR = do
      stack <- get
      liftIO $ setSGR $ case stack of
        []      -> [Reset]
        (tok:_) -> [SetColor Foreground Vivid $ tokenColor tok]


tokenColor :: TokenType -> Color
tokenColor Symbol  = Yellow
tokenColor Keyword = Blue
tokenColor Literal = Green

--------------------------------------------------------------------------------
-- Output Annotation Utilities -------------------------------------------------
--------------------------------------------------------------------------------

-- Literals --------------------------------------------------------------------

intLit :: Int -> ADoc
intLit = literalTok . pprint

integerLit :: Integer -> ADoc
integerLit = literalTok . pprint

floatLit :: Float -> ADoc
floatLit = literalTok . pprint

doubleLit :: Double -> ADoc
doubleLit = literalTok . pprint

stringLit :: String -> ADoc
stringLit = literalTok . pprint . show

-- Single Sybmbols -------------------------------------------------------------

commaSym :: ADoc
commaSym = symbolTok comma

semiSym :: ADoc
semiSym = symbolTok semi

colonSym :: ADoc
colonSym = symbolTok colon

dotSym :: ADoc
dotSym = symbolTok "."

eqSym :: ADoc
eqSym = symbolTok equals


atSym :: ADoc
atSym = symbolTok "@"

doubleEqSym :: ADoc
doubleEqSym = symbolTok "=="

notEqSym :: ADoc
notEqSym = symbolTok "/="

-- Bracket Symbols -------------------------------------------------------------

lparenSym :: ADoc
lparenSym = symbolTok lparen

rparenSym :: ADoc
rparenSym = symbolTok lparen

langleSym :: ADoc
langleSym = symbolTok "<"

rangleSym :: ADoc
rangleSym = symbolTok ">"

lbraceSym :: ADoc
lbraceSym = symbolTok lbrace

rbraceSym :: ADoc
rbraceSym = symbolTok rbrace

lbrackSym :: ADoc
lbrackSym = symbolTok lbrack

rbrackSym :: ADoc
rbrackSym = symbolTok rbrack

-- Bracketing ------------------------------------------------------------------

wrapParens :: ADoc -> ADoc
wrapParens = enclose lparenSym rparenSym

wrapAngles :: ADoc -> ADoc
wrapAngles = enclose langleSym rangleSym

wrapBraces :: ADoc -> ADoc
wrapBraces = enclose lbraceSym rbraceSym

wrapBrackets :: ADoc -> ADoc
wrapBrackets = enclose lbrackSym rbrackSym

--------------------------------------------------------------------------------
-- Other Utility Functions -----------------------------------------------------
--------------------------------------------------------------------------------

enclose :: ADoc -> ADoc -> ADoc -> ADoc
enclose start end doc = start <> doc <> end

encloseSep :: ADoc -> ADoc -> ADoc -> [ADoc] -> ADoc
encloseSep start end sep = enclose start end . hcat . punctuate sep

