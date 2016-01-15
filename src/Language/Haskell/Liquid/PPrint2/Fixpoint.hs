{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.PPrint2.Fixpoint (
    -- * Pretty-Printing Typeclass
    PPrint(..)
  ) where

import qualified Data.Text as T

import Language.Fixpoint.Misc (ListNE)
import Language.Fixpoint.Types hiding (PPrint, pprint, pprintPrec)

import Text.PrettyPrint.Annotated.HughesPJ

import Language.Haskell.Liquid.PPrint2.Base

--------------------------------------------------------------------------------
-- PPrint Instances for Fixpoint AST -------------------------------------------
--------------------------------------------------------------------------------

instance PPrint Constant where
  pprint (I i)   = integerLit i
  pprint (R r)   = doubleLit r
  pprint (L t s) = wrapParens $ keywordTok "lit" <+> stringLit (T.unpack t) <+> pprint s

instance PPrint Brel where
  pprint Eq  = doubleEqSym
  pprint Ne  = notEqSym
  pprint Ueq = symbolTok "~~"
  pprint Une = symbolTok "!~"
  pprint Gt  = symbolTok ">"
  pprint Ge  = symbolTok ">="
  pprint Lt  = symbolTok "<"
  pprint Le  = symbolTok "<="

instance PPrint SymConst where
  pprint (SL s) = stringLit $ T.unpack s

instance PPrint Sort where
  pprint FInt         = keywordTok "int"
  pprint FReal        = keywordTok "real"
  pprint FFrac        = keywordTok "frac"
  pprint FNum         = keywordTok "num"
  pprint (FVar i)     = atSym <> wrapParens (intLit i)
  pprint (FObj x)     = pprint x
  pprint (FFunc n ts) = keywordTok "func" <> wrapParens (intLit n <> commaSym <+> semiList ts)
  pprint (FTC c)      = pprint c
  pprint t@(FApp _ _) = pprintFApp $ fApp' t

pprintFApp :: ListNE Sort -> ADoc
pprintFApp [t] = pprint t
pprintFApp [FTC c, t] | isListTC c = wrapBrackets $ pprint t
pprintFApp ts = encloseSep lparenSym rparenSym space (pprint <$> ts)

instance PPrint FTycon where
  pprint ftc
    | ftc `elem` builtIns = keywordTok ftcDoc
    | otherwise           = ftcDoc
    where
      ftcDoc = pprint $ val $ fTyconSymbol ftc

      builtIns   = [ intFTyCon, boolFTyCon, realFTyCon, numFTyCon
                   , funcFTyCon, strFTyCon, listFTyCon
                   ]
      funcFTyCon = symbolFTycon $ dummyLoc "function"
      strFTyCon  = symbolFTycon $ dummyLoc strConName

--------------------------------------------------------------------------------
-- Fixpoint-Specific Pretty-Printing Utilities ---------------------------------
--------------------------------------------------------------------------------

semiList :: PPrint a => [a] -> ADoc
semiList = encloseSep lbrackSym rbrackSym commaSym . map pprint

