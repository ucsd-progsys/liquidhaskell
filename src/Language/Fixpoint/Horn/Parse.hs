
{-# LANGUAGE DeriveFunctor #-}

module Language.Fixpoint.Horn.Parse (hornP) where

import           Language.Fixpoint.Parse
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Horn.Types   as H
import           Text.Megaparsec                hiding (State)
import           Text.Megaparsec.Char           (char)
import qualified Data.HashMap.Strict            as M

-------------------------------------------------------------------------------
hornP :: Parser (H.Query (), [String])
-------------------------------------------------------------------------------
hornP = do
  hThings <- many hThingP
  pure (mkQuery hThings, [ o | HOpt o <- hThings ])

mkQuery :: [HThing a] -> H.Query a
mkQuery things = H.Query
  { H.qQuals =        [ q | HQual q <- things ]
  , H.qVars  =        [ k | HVar  k <- things ]
  , H.qCstr  = H.CAnd [ c | HCstr c <- things ]
  , H.qCon   = M.fromList  [ (x,t) | HCon x t <- things]
  , H.qDis   = M.fromList  [ (x,t) | HDis x t <- things]
  }

-- | A @HThing@ describes the kinds of things we may see, in no particular order
--   in a .smt2 query file.

data HThing a
  = HQual !F.Qualifier
  | HVar  !(H.Var a)
  | HCstr !(H.Cstr a)

  -- for uninterpred functions and ADT constructors
  | HCon  F.Symbol F.Sort
  | HDis  F.Symbol F.Sort

  | HOpt !String
  deriving (Functor)

hThingP :: Parser (HThing ())
hThingP  = parens body
  where
    body =  HQual <$> (reserved "qualif"     *> hQualifierP)
        <|> HCstr <$> (reserved "constraint" *> hCstrP)
        <|> HVar  <$> (reserved "var"        *> hVarP)
        <|> HOpt  <$> (reserved "fixpoint"   *> stringLiteral)
        <|> HCon  <$> (reserved "constant"   *> symbolP) <*> sortP
        <|> HDis  <$> (reserved "distinct"   *> symbolP) <*> sortP

-------------------------------------------------------------------------------
hCstrP :: Parser (H.Cstr ())
-------------------------------------------------------------------------------
hCstrP = parens body
  where
    body =  H.CAnd  <$> (reserved "and"    *> some hCstrP)
        <|> H.All   <$> (reserved "forall" *> hBindP)       <*> hCstrP
        <|> H.Any   <$> (reserved "exists" *> hBindP)       <*> hCstrP
        <|> H.Head  <$> hPredP                              <*> pure ()

hBindP :: Parser H.Bind
hBindP   = parens $ do
  (x, t) <- symSortP
  p      <- hPredP
  return  $ H.Bind x t p

-------------------------------------------------------------------------------
hPredP :: Parser H.Pred
-------------------------------------------------------------------------------
hPredP = parens body
  where
    body =  H.Var  <$> kvSymP                           <*> some symbolP
        <|> H.PAnd <$> (reserved "and" *> some hPredP)
        <|> H.Reft <$> predP

kvSymP :: Parser F.Symbol
kvSymP = char '$' *> symbolP

-------------------------------------------------------------------------------
-- | Qualifiers
-------------------------------------------------------------------------------
hQualifierP :: Parser F.Qualifier
hQualifierP = do
  pos    <- getSourcePos
  n      <- upperIdP
  params <- parens (some symSortP)
  body   <- parens predP
  return  $ F.mkQual n (mkParam <$> params) body pos

mkParam :: (F.Symbol, F.Sort) -> F.QualParam
mkParam (x, t) = F.QP x F.PatNone t

-------------------------------------------------------------------------------
-- | Horn Variables
-------------------------------------------------------------------------------

hVarP :: Parser (H.Var ())
hVarP = H.HVar <$> kvSymP <*> parens (some (parens sortP)) <*> pure ()

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

symSortP :: Parser (F.Symbol, F.Sort)
symSortP = parens ((,) <$> symbolP <*> sortP)


