{-@ LIQUID "--expect-error-containing=Unknown type constructor" @-}
-- | Type aliases from unqualified imports need to be qualified as well.
module UnqualifiedTypeAlias () where

import qualified Nat1

{-@ test :: INat @-}
test = undefined
