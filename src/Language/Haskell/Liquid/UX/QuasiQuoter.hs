{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Haskell.Liquid.UX.QuasiQuoter (
    -- * LiquidHaskell Specification QuasiQuoter
    lq

    -- * QuasiQuoter Annotations
  , LiquidQuote(..)
  ) where

import Data.Data
import Data.Maybe

import qualified Data.Text as T

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Text.Parsec.Pos

import Language.Fixpoint.Types hiding (Loc)

import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.UX.Tidy

--------------------------------------------------------------------------------
-- LiquidHaskell Specification QuasiQuoter -------------------------------------
--------------------------------------------------------------------------------

lq :: QuasiQuoter
lq = QuasiQuoter
  { quoteExp  = bad
  , quotePat  = bad
  , quoteType = bad
  , quoteDec  = lqDec
  }
  where
    bad = fail "`lq` quasiquoter can only be used as a top-level declaration"

lqDec :: String -> Q [Dec]
lqDec src = do
  pos <- locSourcePos <$> location
  case singleSpecP pos src of
    Left err -> fail . showpp =<< runIO (errorWithContext $ errorToUserError err)
    Right spec -> do
      prg <- pragAnnD ModuleAnnotation $
               conE 'LiquidQuote `appE` dataToExpQ' spec
      let decs = prg : maybeToList (mkSpecDec spec)
      return decs

mkSpecDec :: BPspec -> Maybe Dec
mkSpecDec _ = Nothing

--------------------------------------------------------------------------------
-- QuasiQuoter Annotations -----------------------------------------------------
--------------------------------------------------------------------------------

newtype LiquidQuote = LiquidQuote { liquidQuoteSpec :: BPspec }
                      deriving (Data, Typeable)

--------------------------------------------------------------------------------
-- Template Haskell Utility Functions ------------------------------------------
--------------------------------------------------------------------------------

locSourcePos :: Loc -> SourcePos
locSourcePos loc =
  newPos (loc_filename loc) (fst $ loc_start loc) (snd $ loc_start loc)

dataToExpQ' :: Data a => a -> Q Exp
dataToExpQ' = dataToExpQ (const Nothing `extQ` textToExpQ)

textToExpQ :: T.Text -> Maybe ExpQ
textToExpQ text = Just $ varE 'T.pack `appE` stringE (T.unpack text)

extQ :: (Typeable a, Typeable b) => (a -> q) -> (b -> q) -> a -> q
extQ f g a = maybe (f a) g (cast a)

