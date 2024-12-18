{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Word_LHAssumptions where

import GHC.Word

{-@
embed Word   as int
embed Word8  as int
embed Word16 as int
embed Word32 as int
embed Word64 as int

invariant {v : Word32 | 0 <= v }
invariant {v : Word16 | 0 <= v }
@-}
