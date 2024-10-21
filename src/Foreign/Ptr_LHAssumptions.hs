{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Foreign.Ptr_LHAssumptions where

import Foreign.Ptr

{-@

invariant {v:Foreign.Ptr.Ptr a | 0 <= plen  v }
invariant {v:Foreign.Ptr.Ptr a | 0 <= pbase v }

@-}
