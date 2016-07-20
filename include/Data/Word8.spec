module spec Data.Word8 where

import GHC.Word

invariant {v:GHC.Word.Word8 | 0 <= v }