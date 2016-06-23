module spec Data.Word where

import GHC.Word

invariant {v:Word8  | 0 <= v }
invariant {v:Word32 | 0 <= v }
