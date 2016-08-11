module Language.Haskell.Liquid.Types.Names
  (lenLocSymbol, anyTypeSymbol) where

import Language.Fixpoint.Types

-- RJ: Please add docs
lenLocSymbol :: Located Symbol
lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)

anyTypeSymbol :: Symbol
anyTypeSymbol = symbol ("GHC.Prim.Any" :: String)