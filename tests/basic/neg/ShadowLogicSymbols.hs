-- | LH should not confuse functions with the same name as symbols in
-- | the logic with the corresponding measures
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple"    	@-}

module ShadowLogicSymbols where

import Prelude hiding (not)

not :: Bool -> Bool
not a = a

{-@ reflect shouldBeId @-}
shouldBeId :: Bool -> Bool
shouldBeId x = not x

{-@ lemma :: {shouldBeId False} @-}
lemma = ()