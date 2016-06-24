module spec Data.Word where

import GHC.Word

invariant {v:GHC.Word.Word32 | 0 <= v }