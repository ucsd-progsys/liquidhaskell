module Data.Either_LHAssumptions where

import GHC.Types_LHAssumptions()

{-@
measure isLeft :: Data.Either.Either a b -> Bool
  isLeft (Left x)  = true
  isLeft (Right x) = false
@-}
