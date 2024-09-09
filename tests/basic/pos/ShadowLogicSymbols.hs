-- | You can't shadow names from the logic. You need to fully qualify them to use the symbols you
-- | defined in your specs if they already have a counterpart in the logic.

{-@ LIQUID "--ple"    	@-}
{-@ LIQUID "--reflection"    	@-}

module ShadowLogicSymbols where

import Prelude hiding (not)

{-@ reflect not @-}
not :: Bool -> Bool
not a = a

{-@ lemma :: {ShadowLogicSymbols.not True} @-}
lemma = ()