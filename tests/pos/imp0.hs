module Import0 where

import Language.Haskell.Liquid.Prelude
import Foreign.Storable

-- ERROR goes away if we:
-- import Language.Haskell.Liquid.Foreign

-- We shouldn't have to do so since, 
--   include/Foreign/Storable.Spec
-- has the line:
--   import Language.Haskell.Liquid.Foreign

-- HYPOTHESIS: the import in the spec file above ONLY
--             imports other .spec files... and hence 
--             ignores include/Language/Haskell/Liquid/Foreign.hs 

{-@ inc :: x:Nat -> {v:Nat | v > x} @-}
inc :: Int -> Int
inc x = x + 1
