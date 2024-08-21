{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Internal.Word_LHAssumptions where

{-@
embed GHC.Internal.Word.Word   as int
embed GHC.Internal.Word.Word8  as int
embed GHC.Internal.Word.Word16 as int
embed GHC.Internal.Word.Word32 as int
embed GHC.Internal.Word.Word64 as int

invariant {v : GHC.Internal.Word.Word32 | 0 <= v }
invariant {v : GHC.Internal.Word.Word16 | 0 <= v }
@-}
