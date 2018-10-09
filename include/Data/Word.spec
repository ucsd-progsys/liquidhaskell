module spec Data.Word where

embed Data.Word.Word   as int
embed Data.Word.Word8  as int
embed Data.Word.Word16 as int
embed Data.Word.Word32 as int
embed Data.Word.Word64 as int

invariant {v : Data.Word.Word32 | 0 <= v }
invariant {v : Data.Word.Word16 | 0 <= v }
