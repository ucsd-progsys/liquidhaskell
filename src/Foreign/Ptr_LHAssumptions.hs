{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Ptr_LHAssumptions where

import Foreign.Ptr
import GHC.Ptr_LHAssumptions ()

{-@

invariant {v:Ptr a | 0 <= plen  v }
invariant {v:Ptr a | 0 <= pbase v }

@-}
