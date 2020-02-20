module GHC.Base (module Exports) where

import qualified "base" GHC.Base as Exports

import qualified GHC.CString

-- We cannot really import GHC.Prim, or we would get an error similar to
-- https://gitlab.haskell.org/ghc/ghc/commit/c0270922e0ddd3de549ba7c99244faf431d0740f
-- https://gitlab.haskell.org/ghc/ghc/issues/8320
-- import qualified GHC.Prim

import qualified GHC.Classes
import qualified GHC.Types
