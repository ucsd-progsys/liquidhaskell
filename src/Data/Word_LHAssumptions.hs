module Data.Word_LHAssumptions where

{-@
embed GHC.Word.Word   as int
embed GHC.Word.Word8  as int
embed GHC.Word.Word16 as int
embed GHC.Word.Word32 as int
embed GHC.Word.Word64 as int

invariant {v : GHC.Word.Word32 | 0 <= v }
invariant {v : GHC.Word.Word16 | 0 <= v }
@-}
