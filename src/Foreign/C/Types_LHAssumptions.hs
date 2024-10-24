{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.C.Types_LHAssumptions where

import Foreign.C.Types
import GHC.Int_LHAssumptions()

{-@

embed CInt   as int
embed CSize  as int
embed CULong as int

@-}
