{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Util
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Utility exports (and re-exports) for stitch. This module is meant to
-- be internal -- do not import it if you are not part of the stitch
-- package!
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Util (
  render, toSimpleDoc, maybeParens, ($$),
  Prec, topPrec,
  stripWhitespace, foldl1M,
  allPairs
  ) where

import Text.Parsec
import Text.PrettyPrint.ANSI.Leijen as Pretty

import Data.Char
import Data.List

import Control.Monad

instance Pretty ParseError where
  pretty = text . show

-- | More conspicuous synonym for operator precedence
type Prec = Rational

-- | Precedence for top-level printing
topPrec :: Prec
topPrec = 0

-- | Convert a 'Doc' to a 'String'
render :: Doc -> String
render = flip displayS "" . toSimpleDoc

-- | Convert a 'Doc' to a 'SimpleDoc' for further rendering
toSimpleDoc :: Doc -> SimpleDoc
toSimpleDoc = renderPretty 1.0 78

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc -> Doc
maybeParens True  = parens
maybeParens False = id

-- | Synonym for 'Pretty.<$>'
($$) :: Doc -> Doc -> Doc
($$) = (Pretty.<$>)

-- | (Inefficiently) strips whitespace from a string
stripWhitespace :: String -> String
stripWhitespace = dropWhile isSpace . dropWhileEnd isSpace

-- | Like 'foldl1', but for a monadic computation
foldl1M :: MonadPlus m => (a -> a -> m a) -> [a] -> m a
foldl1M f (x : xs) = foldM f x xs
foldl1M _ _        = mzero

-- | Compute all pairs from the elements in a list; the
-- first element of the pair always occurs before the second
-- in the original list.
allPairs :: [a] -> [(a,a)]
allPairs []     = []
allPairs [_]    = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs
