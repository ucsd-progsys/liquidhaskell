module Duplicate_bind where

import Language.Haskell.Liquid.Prelude

insert key value [] = [(key, value)]
insert _ _ _        = unsafeError ""
