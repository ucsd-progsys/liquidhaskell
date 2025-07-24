{-@ LIQUID "--expect-error-containing=Ambiguous specification symbol" @-}
-- | An error triggered by the ambiguity of a type alias name
-- exported by distinct imported modules. To fix, users need to qualify the use,
-- the import, or both.
module AmbiguousTypeAlias () where

import Nat1 ()
import Nat2 ()

{-@ test :: INat @-}
test :: ()
test = undefined
