-- | This module contains various functions for operating on the @World@ type defined in
--   Language.Haskell.Liquid.Types

module Language.Haskell.Liquid.World (
  -- * Empty world
  empty
  ) where

import Data.Monoid
import Language.Haskell.Liquid.Types
import Language.Fixpoint.Misc

empty   :: World t
empty   = World []

sepConj :: World t -> World t -> World t
sepConj = errorstar "TODO:EFFECTS"

instance Monoid (World t) where
  mempty        = empty
  mappend w1 w2 = sepConj w1 w2


