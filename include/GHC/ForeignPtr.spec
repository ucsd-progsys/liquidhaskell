module spec GHC.ForeignPtr where

import Foreign

mallocPlainForeignPtrBytes :: n:{v:GHC.Types.Int  | v >= 0 } -> (IO {v:(ForeignPtr a) | (plen v) = n})

