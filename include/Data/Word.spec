module spec Data.Word where

import GHC.Word

invariant {v:GHC.Word.Word32 | 0 <= v }
invariant {v:GHC.Word.Word16 | 0 <= v }