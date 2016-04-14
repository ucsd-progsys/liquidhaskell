module Language.Haskell.Liquid.Types.Names
  (lenLocSymbol) where

import Language.Fixpoint.Types

-- RJ: Please add docs
lenLocSymbol :: Located Symbol
lenLocSymbol = dummyLoc $ symbol ("autolen" :: String)
