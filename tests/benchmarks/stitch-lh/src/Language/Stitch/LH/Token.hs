{-# LANGUAGE TupleSections #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Token
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Defines a lexical token
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Token (
  -- * Tokens
  Token(..), LToken(..), noLoc, unLoc, unArithOp, unInt, unBool, unName
  ) where

import Language.Stitch.LH.Util
import Language.Stitch.LH.Op

import Prettyprinter
import Text.Parsec.Pos ( SourcePos, newPos )

import Data.List                      as List

-- | A lexed token
data Token
  = LParen
  | RParen
  | Lambda
  | Dot
  | ArrowTok
  | Colon
  | ArithOp ArithOp
  | IntTok Int
  | BoolTok Bool
  | If
  | Then
  | Else
  | FixTok
  | LetTok
  | InTok
  | Assign
  | Semi
  | Name String
    deriving Eq

-- | Perhaps extract a 'ArithOp'
unArithOp :: Token -> Maybe ArithOp
unArithOp (ArithOp x) = Just x
unArithOp _           = Nothing

-- | Perhaps extract an 'Int'
unInt :: Token -> Maybe Int
unInt (IntTok x) = Just x
unInt _          = Nothing

-- | Perhaps extract an 'Bool'
unBool :: Token -> Maybe Bool
unBool (BoolTok x) = Just x
unBool _           = Nothing

-- | Perhaps extract a 'String'
unName :: Token -> Maybe String
unName (Name x) = Just x
unName _        = Nothing

-- | A lexed token with location information attached
data LToken = L SourcePos Token

-- | Remove location information from an 'LToken'
unLoc :: LToken -> Token
unLoc (L _ t) = t

-- | Decorate a token with an uninformative SourcePos
noLoc :: Token -> LToken
noLoc = L (newPos "noLoc" 0 0)

instance Pretty Token where
  pretty     = getDoc . printingInfo
  prettyList = printTogether . List.map printingInfo

instance Show Token where
  show = show . pretty

instance Pretty LToken where
  pretty     = pretty . unLoc
  prettyList = prettyList . List.map unLoc

instance Show LToken where
  show = render . pretty

type PrintingInfo ann = (Doc ann, Bool, Bool)
   -- the bools say whether or not to include a space before or a space after

alone :: Doc ann -> PrintingInfo ann
alone = (, True, True)

getDoc :: PrintingInfo ann -> Doc ann
getDoc (doc, _, _) = doc

printingInfo :: Token -> PrintingInfo ann
printingInfo LParen          = (pretty '(', True, False)
printingInfo RParen          = (pretty ')', False, True)
printingInfo Lambda          = (pretty '\\', True, False)
printingInfo Dot             = (pretty '.', False, True)
printingInfo ArrowTok        = alone $ pretty "->"
printingInfo Colon           = (pretty ':', False, False)
printingInfo (ArithOp a)     = alone $ pretty a
printingInfo (IntTok i)      = alone $ pretty i
printingInfo (BoolTok True)  = alone $ pretty "true"
printingInfo (BoolTok False) = alone $ pretty "false"
printingInfo If              = alone $ pretty "if"
printingInfo Then            = alone $ pretty "then"
printingInfo Else            = alone $ pretty "else"
printingInfo FixTok          = alone $ pretty "fix"
printingInfo LetTok          = alone $ pretty "let"
printingInfo InTok           = alone $ pretty "in"
printingInfo Assign          = alone $ pretty "="
printingInfo Semi            = (pretty ';', False, True)
printingInfo (Name t)        = alone $ pretty t

printTogether :: [PrintingInfo ann] -> Doc ann
printTogether []  = mempty
printTogether pis = getDoc $ List.foldl1 combine pis
  where
    combine (doc1, before_space, inner_space1) (doc2, inner_space2, after_space)
      | inner_space1 && inner_space2
      = (doc1 <+> doc2, before_space, after_space)

      | otherwise
      = (doc1 <> doc2, before_space, after_space)
