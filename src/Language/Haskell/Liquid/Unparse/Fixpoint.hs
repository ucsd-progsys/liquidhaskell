{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Unparse.Fixpoint (
    -- * The Unparse Typeclass
    Unparse(..)
  ) where

import qualified Data.Text as T

import Language.Fixpoint.Misc (ListNE)
import Language.Fixpoint.Types

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.Haskell.Liquid.Unparse.Base

--------------------------------------------------------------------------------
-- Unparse Instances for Fixpoint AST ------------------------------------------
--------------------------------------------------------------------------------

instance Unparse Constant where
  unparse (I i)   = integer' i
  unparse (R r)   = double' r
  unparse (L t s) = parens' $ keywordToken "lit" <+> stringLit (T.unpack t) <+> unparse s

instance Unparse Brel where
  unparse Eq  = doubleEquals
  unparse Ne  = notEquals
  unparse Ueq = symbolToken "~~"
  unparse Une = symbolToken "!~"
  unparse Gt  = symbolToken ">"
  unparse Ge  = symbolToken ">="
  unparse Lt  = symbolToken "<"
  unparse Le  = symbolToken "<="

instance Unparse SymConst where
  unparse (SL s) = stringLit $ T.unpack s

instance Unparse Sort where
  unparse FInt         = keywordToken "int"
  unparse FReal        = keywordToken "real"
  unparse FFrac        = keywordToken "frac"
  unparse FNum         = keywordToken "num"
  unparse (FVar i)     = atSign <> parens' (int' i)
  unparse (FObj x)     = text $ T.unpack $ symbolText x
  unparse (FFunc n ts) = text "func" <> parens' (int' n <> comma <+> semiList ts)
  unparse (FTC c)      = unparse c
  unparse t@(FApp _ _) = unparseFApp $ fApp' t

unparseFApp :: ListNE Sort -> Doc
unparseFApp [t] = unparse t
unparseFApp [FTC c, t] | isListTC c = brackets' $ unparse t
unparseFApp ts = encloseSep lparen' rparen' space (unparse <$> ts)

-- TODO: Remove when https://github.com/ucsd-progsys/liquid-fixpoint/pull/180
--       is merged.
fApp' :: Sort -> ListNE Sort
fApp' = go []
  where
    go acc (FApp t1 t2) = go (t2 : acc) t1
    go acc t            = t : acc

instance Unparse FTycon where
  unparse ftc
    | ftc `elem` builtIns = keywordToken' tcDoc
    | otherwise           = tcDoc
    where
      tcDoc = text $ symbolString $ val $ fTyconSymbol ftc

      builtIns   = [ intFTyCon, boolFTyCon, realFTyCon, numFTyCon
                   , funcFTyCon, strFTyCon, listFTyCon
                   ]
      funcFTyCon = symbolFTycon $ dummyLoc "function"
      strFTyCon  = symbolFTycon $ dummyLoc strConName

--------------------------------------------------------------------------------
-- Fixpoint-Specific Unparsing Utilities ---------------------------------------
--------------------------------------------------------------------------------

semiList :: Unparse a => [a] -> Doc
semiList = encloseSep lbracket' rbracket' comma' . map unparse

